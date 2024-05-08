// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, ECALL_INSTRUCTION_LENGTH};
use crate::core::control_data::HypervisorHart;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Registers a shared nested acceleration (NACL) memory.
pub struct NaclSetupSharedMemory {
    shared_memory_base_address: usize,
}

impl NaclSetupSharedMemory {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { shared_memory_base_address: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SetSharedMemory(self))
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        debug!("Registering NACL shared memory at {:x}", self.shared_memory_base_address);
        let sbi_response = NonConfidentialMemoryAddress::new(self.shared_memory_base_address as *mut usize)
            .and_then(|address| hypervisor_hart.set_shared_memory(address))
            .map_or_else(|_error| 1, |_| 0);

        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + ECALL_INSTRUCTION_LENGTH;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, sbi_response);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, 0);
    }
}
