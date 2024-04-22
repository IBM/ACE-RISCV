// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct NaclHandler {
    shared_memory_base_address: usize,
}

impl NaclHandler {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        // Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GPRs). GPRs
        // might carry SBI- or MMIO-related reponses, so using GPRs would destroy the communication between the hypervisor and confidential
        // VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V NACL extension that solves these problems by
        // using shared memory region in which the SBI- and MMIO-related information is transfered.
        Self { shared_memory_base_address: hypervisor_hart.csrs().vstvec.read() }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow.hack_restore_original_gprs();
        let sbi_response = match non_confidential_flow.set_shared_memory(self.shared_memory_base_address) {
            Ok(()) => ApplyToHypervisor::SbiResponse(SbiResponse::success(0)),
            Err(error) => error.into_non_confidential_transformation(),
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(sbi_response)
    }
}
