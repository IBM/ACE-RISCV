// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::sbi::CovgExtension;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ResumableOperation};
use crate::non_confidential_flow::DeclassifyToHypervisor;

pub struct DebugRequest {
    a0: usize,
    a1: usize,
}

impl DebugRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            a0: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            a1: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow
            .set_resumable_operation(ResumableOperation::SbiRequest())
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(SbiRequest::new(
                CovgExtension::EXTID,
                CovgExtension::SBI_EXT_COVG_DEBUG,
                self.a0,
                self.a1,
            )));
    }
}
