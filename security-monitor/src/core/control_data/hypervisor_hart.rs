// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::riscv::specification::SR_FS;
use crate::core::architecture::specification::SR_FS_DIRTY;
use crate::core::architecture::{
    ControlStatusRegisters, GeneralPurposeRegisters, HartArchitecturalState, IsaExtension, SupervisorTimerExtension,
};
use crate::core::configuration::Configuration;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::error::Error;

/// Represents a state of the hypervisor hart at the time the hypervisor trapped in the security monitor.
#[repr(C)]
pub struct HypervisorHart {
    // Safety: HypervisorHart and ConfidentialHart must both start with the HartArchitecturalState element because based on this we
    // automatically calculate offsets of registers' and CSRs' for the asm code.
    hypervisor_hart_state: HartArchitecturalState,
    // Shared memory between the hypervisor and confidential hart is located in non-confidential memory (owned by the hypervisor).
    // Hypervisor sets this shared memory before creating any confidential VM. This shared memory is used to pass data/arguments of calls
    // to the security monitor (COVH) or to the hypervisor (COVG).
    shared_memory: NaclSharedMemory,
    // Memory protector that configures the hardware memory isolation component to allow only memory accesses
    // to the memory region owned by the hypervisor.
    hypervisor_memory_protector: HypervisorMemoryProtector,
}

impl HypervisorHart {
    pub fn new(hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self {
            hypervisor_hart_state: HartArchitecturalState::empty(),
            shared_memory: NaclSharedMemory::uninitialized(),
            hypervisor_memory_protector,
        }
    }

    /// Saves the state of the hypervisor hart in the main memory. This is part of the heavy context switch.
    pub fn save_in_main_memory(&mut self) {
        self.csrs_mut().save_in_main_memory();
        // below unsafe is ok because we ensured during the initialization that Sstc extension is present.
        unsafe {
            self.sstc_mut().save_in_main_memory();
        }

        if Configuration::is_extension_supported(IsaExtension::FloatingPointExtension) {
            if (self.csrs().mstatus.read() & (SR_FS_DIRTY | SR_FS)) > 0 {
                // below unsafe is ok because we checked that FPU hardware is available and we enabled it in mstatus.
                unsafe {
                    self.hypervisor_hart_state.fprs_mut().save_in_main_memory();
                }
            }
        }
    }

    /// Restores the state of the hypervisor hart from the main memory. This is part of the heavy context switch.
    pub fn restore_from_main_memory(&mut self) {
        self.csrs().restore_from_main_memory();
        // below unsafe is ok because we ensured during the initialization that Sstc extension is present.
        unsafe { self.sstc().restore_from_main_memory() };

        if Configuration::is_extension_supported(IsaExtension::FloatingPointExtension) {
            self.csrs().mstatus.read_and_set_bits(SR_FS);
            // below unsafe is ok because we checked that FPU hardware is available and we enabled it in mstatus.
            unsafe { self.hypervisor_hart_state.fprs_mut().restore_from_main_memory() };
        }
    }

    pub fn set_shared_memory(&mut self, base_address: NonConfidentialMemoryAddress) -> Result<(), Error> {
        self.shared_memory.set(base_address)
    }

    pub unsafe fn enable_hypervisor_memory_protector(&self) {
        self.hypervisor_memory_protector.enable(self.csrs().hgatp.read_from_main_memory())
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

    pub fn sstc(&self) -> &SupervisorTimerExtension {
        self.hypervisor_hart_state.sstc()
    }

    pub fn sstc_mut(&mut self) -> &mut SupervisorTimerExtension {
        self.hypervisor_hart_state.sstc_mut()
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
}
