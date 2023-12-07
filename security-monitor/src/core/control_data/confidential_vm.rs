// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HardwareHart};
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::error::Error;
use alloc::vec::Vec;

const MAX_HASH_SIZE: usize = 512; // 512b for SHA-512

#[derive(PartialEq, Eq, Hash, Debug, PartialOrd, Ord, Copy, Clone)]
pub struct ConfidentialVmId(usize);

impl ConfidentialVmId {
    pub fn new(value: usize) -> Self {
        Self(value)
    }
    pub fn usize(&self) -> usize {
        self.0
    }
}

pub struct ConfidentialVm {
    id: ConfidentialVmId,
    _measurements: [Measurement; 4],
    confidential_harts: Vec<ConfidentialHart>,
    memory_protector: ConfidentialVmMemoryProtector,
}

impl ConfidentialVm {
    pub fn new(
        id: ConfidentialVmId, mut confidential_harts: Vec<ConfidentialHart>,
        mut memory_protector: ConfidentialVmMemoryProtector,
    ) -> Self {
        memory_protector.set_confidential_vm_id(id);
        confidential_harts.iter_mut().for_each(|confidential_hart| confidential_hart.set_confidential_vm_id(id));
        Self { id, _measurements: [Measurement::empty(); 4], confidential_harts, memory_protector }
    }

    pub fn memory_protector_mut(&mut self) -> &mut ConfidentialVmMemoryProtector {
        &mut self.memory_protector
    }

    /// Steals a confidential hart from the confidential VM and assigns it to the hardware hart. The
    /// hardware memory isolation mechanism is reconfigured to enforce memory access control for the
    /// confidential VM. Error is returns if the confidential VM's virtual hart has been already stolen.
    ///
    /// Guarantees:
    /// * If confidential hart is assigned to the hardware hart, then the hardware hart is configured to enforce memory
    ///   access control of the confidential VM.
    pub fn steal_confidential_hart(
        &mut self, confidential_hart_id: usize, hardware_hart: &mut HardwareHart,
    ) -> Result<(), Error> {
        let confidential_hart = self.confidential_harts.get(confidential_hart_id).ok_or(Error::InvalidHartId())?;
        // The hypervisor might try to schedule the same confidential hart on different physical harts. We detect it
        // because after a confidential_hart is scheduled for the first time, its token is stolen and the
        // ConfidentialVM is left with a dummy confidential_hart. A dummy confidential hart is a hart not associated
        // with any confidential vm.
        assure_not!(confidential_hart.is_dummy(), Error::RunningVHart())?;
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
        // It is safe to invoke below unsafe code because at this point we are in the confidential flow part of the
        // finite state machine and the virtual hart is assigned to the hardware hart. We must reconfigure the hardware
        // memory isolation mechanism to enforce that the confidential virtual machine has access only to the memory
        // regions it owns.
        unsafe { self.memory_protector.enable() };
        Ok(())
    }

    pub fn return_confidential_hart(&mut self, hardware_hart: &mut HardwareHart) {
        assert!(!hardware_hart.confidential_hart.is_dummy());
        assert!(Some(self.id) == hardware_hart.confidential_hart().confidential_vm_id());
        let confidential_hart_id = hardware_hart.confidential_hart.confidential_hart_id();
        core::mem::swap(&mut hardware_hart.confidential_hart, &mut self.confidential_harts[confidential_hart_id]);
        // It is safe to reconfigure the memory access control configuration to enable access to memory regions owned
        // by the hypervisor because we are now transitioning into the non-confidential flow part of the finite state
        // machine where the hardware hart is associated with a dummy virtual hart.
        unsafe { hardware_hart.enable_hypervisor_memory_protector() };
    }

    pub fn is_running(&self) -> bool {
        self.confidential_harts.iter().filter(|confidential_hart| confidential_hart.is_dummy()).count() > 0
    }
}

#[derive(Clone, Copy)]
pub struct Measurement {
    pub value: [u8; MAX_HASH_SIZE / 8],
}

impl Measurement {
    pub const fn empty() -> Measurement {
        Self { value: [0u8; MAX_HASH_SIZE / 8] }
    }
}
