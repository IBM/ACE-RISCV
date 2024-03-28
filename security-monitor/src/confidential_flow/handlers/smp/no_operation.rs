// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};
use crate::core::control_data::ConfidentialHart;

#[derive(PartialEq, Debug, Clone)]
pub struct NoOperation {}

impl NoOperation {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    /// Implements NOP (no operation) for calls that are not implemented by the security monitor but should be supported due to
    /// compatibility reasons. These calls are remote fence SBI calls required in systems supporting nested virtualization.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialVm::SbiResponse(SbiResponse::success(0)))
    }
}
