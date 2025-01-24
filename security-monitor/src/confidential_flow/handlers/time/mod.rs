// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::specification::WFI_INSTRUCTION;
use crate::core::architecture::{GeneralPurposeRegister, CSR};
use crate::core::control_data::{ConfidentialHart, ResumableOperation};
use crate::core::timer_controller::TimerController;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles virtual instruction trap that occured during execution of the confidential hart.
pub struct SetTimer {
    ncycle: usize,
}

impl SetTimer {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { ncycle: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        TimerController::try_write(|controller| Ok(controller.set_next_event_for_vs_mode(&mut confidential_flow, self.ncycle))).unwrap();
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::success()))
    }
}
