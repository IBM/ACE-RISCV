// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult};

pub fn handle(hypercall_result: SbiResult, confidential_flow: ConfidentialFlow) -> ! {
    let transformation = ExposeToConfidentialVm::SbiResult(hypercall_result);
    confidential_flow.exit_to_confidential_vm(transformation)
}
