// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::core::timer_controller::TimerController;

/// Handles virtual instruction trap that occured during execution of the confidential hart.
pub struct SetTimer {
    ncycle: usize,
}

impl SetTimer {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { ncycle: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        TimerController::new(&mut confidential_flow).set_next_event_for_vs_mode(self.ncycle);
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::success()))
    }
}
