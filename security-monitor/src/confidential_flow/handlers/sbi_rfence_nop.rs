// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult};

/// Implements NOP (no operation) for calls that are not implemented by the security monitor but should be supported due to compatibility
/// reasons. These calls are remote fence SBI calls required in systems supporting nested virtualization.
pub fn handle(confidential_flow: ConfidentialFlow) -> ! {
    confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiResult(SbiResult::success(0)))
}
