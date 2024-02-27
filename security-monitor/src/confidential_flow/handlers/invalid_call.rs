// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::CSR;
use crate::error::Error;

/// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
/// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
pub fn handle(confidential_flow: ConfidentialFlow) -> ! {
    let mcause = CSR.mcause.read();
    let transformation = Error::InvalidCall(mcause).into_confidential_transformation();
    confidential_flow.exit_to_confidential_hart(transformation)
}
