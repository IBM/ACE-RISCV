// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialVm, ConfidentialVmId};
use crate::error::{Error, NOT_INITIALIZED_CONTROL_DATA};
use alloc::collections::BTreeMap;
use spin::{Mutex, MutexGuard, Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

/// The control data region is located in the confidential memory. It is visible only to the security monitor. The
/// security monitor uses it to store persistent confidential VM information.
///
/// Access to it variable is exposed to other modules with try_read_*() and try_write_*(). These functions synchronize
/// accesses to the control data region descriptor requested from multiple physical harts.
pub static CONTROL_DATA: Once<RwLock<ControlData>> = Once::new();

pub struct ControlData {
    confidential_vms: BTreeMap<ConfidentialVmId, Mutex<ConfidentialVm>>,
}

impl ControlData {
    pub fn new() -> Self {
        Self { confidential_vms: BTreeMap::new() }
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
        match self.confidential_vms.contains_key(&id) {
            false => {
                self.confidential_vms.insert(id, Mutex::new(confidential_vm));
                Ok(id)
            }
            true => Err(Error::InvalidConfidentialVmId()),
        }
    }

    pub fn confidential_vm(&self, id: ConfidentialVmId) -> Result<MutexGuard<'_, ConfidentialVm>, Error> {
        self.confidential_vms.get(&id).ok_or(Error::InvalidConfidentialVmId()).and_then(|v| Ok(v.lock()))
    }

    pub fn remove_confidential_vm(confidential_vm_id: ConfidentialVmId) -> Result<(), Error> {
        ControlData::try_write(|control_data| {
            assure!(control_data.confidential_vm(confidential_vm_id)?.are_all_harts_shutdown(), Error::HartAlreadyRunning())?;
            debug!("ConfidentialVM[{:?}] removed from the control data structure", confidential_vm_id);
            control_data.confidential_vms.remove(&confidential_vm_id).ok_or(Error::InvalidConfidentialVmId())
        })?
        .into_inner()
        .deallocate();
        Ok(())
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, ControlData>) -> Result<F, Error> {
        op(&CONTROL_DATA.get().expect(NOT_INITIALIZED_CONTROL_DATA).read())
    }

    pub fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, ControlData>) -> Result<F, Error> {
        op(&mut CONTROL_DATA.get().expect(NOT_INITIALIZED_CONTROL_DATA).write())
    }

    pub fn try_confidential_vm<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|mr| op(mr.confidential_vm(confidential_vm_id)?))
    }

    pub fn try_confidential_vm_mut<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|m| op(m.confidential_vm(confidential_vm_id)?))
    }
}
