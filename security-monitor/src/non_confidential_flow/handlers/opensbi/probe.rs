// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::{GeneralPurposeRegister, *};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::non_confidential_flow::handlers::opensbi::delegate::OpensbiHandler;
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

pub struct SbiExtensionProbe {
    extension_id: usize,
    opensbi_handler: OpensbiHandler,
}

impl SbiExtensionProbe {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            extension_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
            opensbi_handler: OpensbiHandler::from_hypervisor_hart(hypervisor_hart),
        }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        let response = match self.extension_id {
            CoveExtension::EXTID | NaclExtension::EXTID => {
                let transformation = ApplyToHypervisor::SbiResponse(SbiResponse::success(1));
                non_confidential_flow.apply_and_exit_to_hypervisor(transformation)
            }
            _ => self.opensbi_handler.handle(non_confidential_flow),
        };
    }
}
