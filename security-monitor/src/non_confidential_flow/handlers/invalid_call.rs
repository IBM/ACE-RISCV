// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

pub fn handle(non_confidential_flow: NonConfidentialFlow, extension_id: usize, function_id: usize) -> ! {
    let mcause = riscv::register::mcause::read().code();
    let transformation = Error::InvalidCall(mcause, extension_id, function_id).into_non_confidential_transformation();

    non_confidential_flow.exit_to_hypervisor(transformation)
}
