// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::ConfidentialHart;
use crate::core::timer_controller::TimerController;

pub struct ReadTime {
    htimedelta: usize,
}

impl ReadTime {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { htimedelta: confidential_hart.csrs().htimedelta }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::success_with_code(
            TimerController::read_virt_time(self.htimedelta),
        )))
    }
}
