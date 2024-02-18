// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, SbiRequest, SbiResult};

/// Handles a hypercall from a confidential hart to hypervisor.
pub fn handle(sbi_request: SbiRequest, confidential_flow: ConfidentialFlow) -> ! {
    debug!("Debug: a0={} a1={} a2={}", sbi_request.a0(), sbi_request.a1(), sbi_request.a2());

    let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(0));
    confidential_flow.exit_to_confidential_hart(transformation)
}
