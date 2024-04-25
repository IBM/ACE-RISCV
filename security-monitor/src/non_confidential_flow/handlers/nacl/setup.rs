// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct SetupNacl {
    shared_memory_base_address: usize,
}

impl SetupNacl {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { shared_memory_base_address: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        debug!("Setting up the NACL shared memory {:x}", self.shared_memory_base_address);
        let sbi_response = match non_confidential_flow.set_shared_memory(self.shared_memory_base_address) {
            Ok(()) => ApplyToHypervisor::SbiResponse(SbiResponse::success(0)),
            Err(error) => error.into_non_confidential_transformation(),
        };
        non_confidential_flow.apply_and_exit_to_hypervisor(sbi_response)
    }
}
