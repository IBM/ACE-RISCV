// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::error::Error;

pub fn handle(confidential_flow: ConfidentialFlow, extension_id: usize, function_id: usize) -> ! {
    let mcause = riscv::register::mcause::read().code();

    let transformation = Error::InvalidCall(mcause, extension_id, function_id).into_confidential_transformation();

    confidential_flow.exit_to_confidential_vm(transformation)
}
