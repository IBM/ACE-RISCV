// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::specification::CAUSE_VIRTUAL_SUPERVISOR_ECALL;
use crate::core::architecture::sbi::CovgExtension;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, HypervisorHart, ResumableOperation};
use crate::non_confidential_flow::DeclassifyToHypervisor;

pub struct DebugRequest {
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
}

impl DebugRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let a0 = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let a1 = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let a2 = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let a3 = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        Self { a0, a1, a2, a3 }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let r = SbiRequest::new(CovgExtension::EXTID, CovgExtension::SBI_EXT_COVG_DEBUG, self.a0, self.a1);

        confidential_flow
            .set_resumable_operation(ResumableOperation::SbiRequest())
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(r));
    }
}
