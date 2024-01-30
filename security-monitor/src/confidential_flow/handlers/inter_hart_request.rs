// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, InterHartRequest, SbiResult};

/// Injects an InterHartRequest to confidential harts specified as part of the request.
pub fn handle(inter_hart_request: InterHartRequest, mut confidential_flow: ConfidentialFlow) -> ! {
    let transformation = confidential_flow
        .broadcast_inter_hart_request(inter_hart_request.clone())
        .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
        .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_vm(transformation)
}
