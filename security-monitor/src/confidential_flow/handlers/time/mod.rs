// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::specification::WFI_INSTRUCTION;
use crate::core::architecture::{GeneralPurposeRegister, CSR};
use crate::core::control_data::{ConfidentialHart, ResumableOperation};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles virtual instruction trap that occured during execution of the confidential hart.
pub struct SetTimer {
    a0: usize,
}

impl SetTimer {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let a0 = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        Self { a0 }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let rr = SbiRequest::new(0x54494D45, 0, self.a0, 0);

        debug!(
            "set timer={:x} | time={:x} mepc={:x}",
            self.a0,
            CSR.time.read(),
            confidential_flow.confidential_hart_mut().csrs().mepc.read_from_main_memory()
        );
        confidential_flow
            .set_resumable_operation(ResumableOperation::SbiRequest())
            .into_non_confidential_flow()
            .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(rr))
    }
}
