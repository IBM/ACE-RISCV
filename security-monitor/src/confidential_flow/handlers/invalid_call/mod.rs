// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ConfidentialHart;
use crate::error::Error;

pub struct InvalidCall {
    mcause: usize,
}

impl InvalidCall {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { mcause: confidential_hart.csrs().mcause.read() }
    }

    /// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
    /// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = Error::InvalidCall(self.mcause).into_confidential_transformation();
        confidential_flow.exit_to_confidential_hart(transformation)
    }
}
