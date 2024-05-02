// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{ControlStatusRegisters, GeneralPurposeRegisters, HartArchitecturalState, NaclSharedMemory};
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::error::Error;

/// Represents a state of the hypervisor hart at the time the hypervisor called the security monitor.
#[repr(C)]
pub struct HypervisorHart {
    // Safety: HypervisorHart and ConfidentialHart must both start with the HartArchitecturalState element
    // because based on this we automatically calculate offsets of registers' and CSRs' for the asm code.
    hypervisor_hart_state: HartArchitecturalState,
    // Shared memory between the hypervisor and confidential hart is located in non-confidential memory (owned by the hypervisor).
    // Hypervisor sets this shared memory before creating any confidential VM.
    shared_memory: NaclSharedMemory,
    // Memory protector that configures the hardware memory isolation component to allow only memory accesses
    // to the memory region owned by the hypervisor.
    hypervisor_memory_protector: HypervisorMemoryProtector,
}

impl HypervisorHart {
    pub fn new(id: usize, hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self {
            hypervisor_hart_state: HartArchitecturalState::empty(id),
            shared_memory: NaclSharedMemory::uninitialized(),
            hypervisor_memory_protector,
        }
    }

    pub fn address(&self) -> usize {
        core::ptr::addr_of!(self.hypervisor_hart_state) as usize
    }

    pub fn gprs(&self) -> &GeneralPurposeRegisters {
        self.hypervisor_hart_state.gprs()
    }

    pub fn gprs_mut(&mut self) -> &mut GeneralPurposeRegisters {
        self.hypervisor_hart_state.gprs_mut()
    }

    pub fn csrs(&self) -> &ControlStatusRegisters {
        self.hypervisor_hart_state.csrs()
    }

    pub fn csrs_mut(&mut self) -> &mut ControlStatusRegisters {
        self.hypervisor_hart_state.csrs_mut()
    }

    pub fn hypervisor_hart_state(&self) -> &HartArchitecturalState {
        &self.hypervisor_hart_state
    }

    pub fn shared_memory(&self) -> &NaclSharedMemory {
        &self.shared_memory
    }

    pub fn shared_memory_mut(&mut self) -> &mut NaclSharedMemory {
        &mut self.shared_memory
    }

    pub fn set_shared_memory(&mut self, base_address: NonConfidentialMemoryAddress) -> Result<(), Error> {
        self.shared_memory.set(base_address)?;
        Ok(())
    }

    pub unsafe fn enable_hypervisor_memory_protector(&self) {
        self.hypervisor_memory_protector.enable(self.csrs().hgatp.read_value())
    }
}
