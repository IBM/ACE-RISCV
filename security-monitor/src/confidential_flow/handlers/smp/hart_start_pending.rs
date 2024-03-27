// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStartPending {}

impl SbiHsmHartStartPending {
    pub fn new() -> Self {
        Self {}
    }

    /// Returns the lifecycle state of the confidential hart as defined in the HART get status (FID #2) function of the SBI's HSM extension.
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.start_confidential_hart();
        confidential_flow.exit_to_confidential_hart(ApplyToConfidentialVm::Nothing())
    }
}
