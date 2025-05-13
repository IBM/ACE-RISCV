// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialVm, ConfidentialVmId};
use crate::error::Error;
use alloc::collections::BTreeMap;
use spin::{Mutex, MutexGuard, Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

static CONTROL_DATA_STORAGE: Once<RwLock<ControlDataStorage>> = Once::new();

/// The control data region is located in the confidential memory. It is visible only to the security monitor. The
/// security monitor uses it to store persistent confidential VM information.
///
/// Access to it variable is exposed to other modules with try_read_*() and try_write_*(). These functions synchronize
/// accesses to the control data region descriptor requested from multiple physical harts.
pub struct ControlDataStorage {
    confidential_vms: BTreeMap<ConfidentialVmId, RwLock<ConfidentialVm>>,
}

impl ControlDataStorage {
    const NOT_INITIALIZED: &'static str = "Bug: Control data not initialized";

    pub fn initialize() -> Result<(), Error> {
        let control_data = Self { confidential_vms: BTreeMap::new() };
        ensure_not!(CONTROL_DATA_STORAGE.is_completed(), Error::Reinitialization())?;
        CONTROL_DATA_STORAGE.call_once(|| RwLock::new(control_data));
        Ok(())
    }

    pub fn unique_id(&self) -> Result<ConfidentialVmId, Error> {
        self.confidential_vms
            .keys()
            .max()
            .map(|v| v.usize().checked_add(1))
            .unwrap_or(Some(0))
            .and_then(|max_id| Some(ConfidentialVmId::new(max_id)))
            .ok_or(Error::TooManyConfidentialVms())
    }

    pub fn insert_confidential_vm(&mut self, confidential_vm: ConfidentialVm) -> Result<ConfidentialVmId, Error> {
        let id = confidential_vm.confidential_vm_id();
        ensure!(!self.confidential_vms.contains_key(&id), Error::InvalidConfidentialVmId())?;
        self.confidential_vms.insert(id, RwLock::new(confidential_vm));
        Ok(id)
    }

    pub fn confidential_vm(&self, id: ConfidentialVmId) -> Result<RwLockReadGuard<'_, ConfidentialVm>, Error> {
        Ok(self.confidential_vms.get(&id).ok_or(Error::InvalidConfidentialVmId()).and_then(|v| Ok(v.read()))?)
    }

    pub fn confidential_vm_mut(&self, id: ConfidentialVmId) -> Result<RwLockWriteGuard<'_, ConfidentialVm>, Error> {
        self.confidential_vms.get(&id).ok_or(Error::InvalidConfidentialVmId()).and_then(|v| Ok(v.write()))
    }

    pub fn remove_confidential_vm(confidential_vm_id: ConfidentialVmId) -> Result<(), Error> {
        ControlDataStorage::try_write(|control_data| {
            ensure!(control_data.confidential_vm(confidential_vm_id)?.is_vm_executing(), Error::HartAlreadyRunning())?;
            debug!("Removing ConfidentialVM[{:?}] from the control data structure", confidential_vm_id);
            control_data.confidential_vms.remove(&confidential_vm_id).ok_or(Error::InvalidConfidentialVmId())
        })
        .and_then(|vm| Ok(vm.into_inner().deallocate()))
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, ControlDataStorage>) -> Result<F, Error> {
        op(&CONTROL_DATA_STORAGE.get().expect(Self::NOT_INITIALIZED).read())
    }

    pub fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, ControlDataStorage>) -> Result<F, Error> {
        op(&mut CONTROL_DATA_STORAGE.get().expect(Self::NOT_INITIALIZED).write())
    }

    pub fn try_confidential_vm<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(RwLockReadGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|mr| op(mr.confidential_vm(confidential_vm_id)?))
    }

    pub fn try_confidential_vm_mut<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(RwLockWriteGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|m| op(m.confidential_vm_mut(confidential_vm_id)?))
    }
}
