// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, PendingRequest, SbiRequest};

pub fn handle(sbi_request: SbiRequest, confidential_flow: ConfidentialFlow) -> ! {
    confidential_flow
        .set_pending_request(PendingRequest::SbiRequest())
        .into_non_confidential_flow()
        .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request))
}
