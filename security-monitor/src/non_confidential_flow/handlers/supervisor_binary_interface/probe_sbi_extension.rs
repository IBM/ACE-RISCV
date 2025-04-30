// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::{CovhExtension, NaclExtension};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

pub struct ProbeSbiExtension {
    extension_id: usize,
}

impl ProbeSbiExtension {
    pub fn from_hypervisor_hart(hypervisor_hart: &mut HypervisorHart) -> Self {
        Self { extension_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> ! {
        match self.extension_id {
            CovhExtension::EXTID | NaclExtension::EXTID => {
                non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::SbiResponse(SbiResponse::success_with_code(1)))
            }
            _ => non_confidential_flow.delegate_to_opensbi(),
        }
    }
}
