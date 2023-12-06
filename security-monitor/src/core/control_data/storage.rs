// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, ConfidentialVm, ConfidentialVmId};
use crate::core::memory_partitioner::RootPageTable;
use crate::error::{Error, NOT_INITIALIZED_CONTROL_DATA};
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
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

    /// This function persists a confidential VM inside the control data. A unique identifier is calculated and assigned
    /// to it. This identifier is not secret and reflects the number of confidential VMs that have been created up to
    /// now. The maximum allowed number of confidential VMs created is limited by the size of the `usize` type.
    pub fn store_confidential_vm(
        confidential_harts: Vec<ConfidentialHart>, root_page_table: RootPageTable,
    ) -> Result<ConfidentialVmId, Error> {
        Self::try_write(|control_data| {
            control_data
                .confidential_vms
                .keys()
                .max()
                .map(|v| v.usize().checked_add(1))
                .unwrap_or(Some(0))
                .and_then(|max_id| {
                    let id = ConfidentialVmId::new(max_id);
                    let confidential_vm = ConfidentialVm::new(id, confidential_harts, root_page_table);
                    control_data.confidential_vms.insert(id, Mutex::new(confidential_vm));
                    Some(id)
                })
                .ok_or(Error::ReachedMaximumNumberOfCvms())
        })
    }

    pub fn confidential_vm(&self, id: ConfidentialVmId) -> Option<MutexGuard<'_, ConfidentialVm>> {
        self.confidential_vms.get(&id).and_then(|v| v.try_lock())
    }

    pub fn remove_confidential_vm(
        &mut self, confidential_vm_id: ConfidentialVmId,
    ) -> Result<Mutex<ConfidentialVm>, Error> {
        self.confidential_vms.remove(&confidential_vm_id).ok_or(Error::InvalidConfidentialVmId())
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, ControlData>) -> Result<F, Error> {
        CONTROL_DATA
            .get()
            .expect(NOT_INITIALIZED_CONTROL_DATA)
            .try_read()
            .ok_or(Error::OptimisticLocking())
            .and_then(|ref control_data| op(control_data))
    }

    pub fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, ControlData>) -> Result<F, Error> {
        CONTROL_DATA
            .get()
            .expect(NOT_INITIALIZED_CONTROL_DATA)
            .try_write()
            .ok_or(Error::OptimisticLocking())
            .and_then(|ref mut control_data| op(control_data))
    }

    pub fn try_confidential_vm<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|mr| op(mr.confidential_vm(confidential_vm_id).ok_or(Error::InvalidConfidentialVmId())?))
    }

    pub fn try_confidential_vm_mut<F, O>(confidential_vm_id: ConfidentialVmId, op: O) -> Result<F, Error>
    where O: FnOnce(MutexGuard<'_, ConfidentialVm>) -> Result<F, Error> {
        Self::try_read(|m| op(m.confidential_vm(confidential_vm_id).ok_or(Error::InvalidConfidentialVmId())?))
    }
}
