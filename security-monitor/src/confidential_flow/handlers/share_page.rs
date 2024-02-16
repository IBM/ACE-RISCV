// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, PendingRequest, SbiRequest, SharePageRequest};
use crate::error::Error;

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows to the hypervisor when the sharing of the given `guest physical address` is allowed. The hypervisor is requested to
/// allocate a page of non-confidential memory and return back the `host physical address` of this page. Control flows back to the
/// confidential hart if the request was invalid, e.g., the `guest physical address` was not correct.
pub fn handle(request: Result<(SharePageRequest, SbiRequest), Error>, confidential_flow: ConfidentialFlow) -> ! {
    match request {
        Ok((share_page_request, sbi_request)) => confidential_flow
            .set_pending_request(PendingRequest::SharePage(share_page_request))
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request)),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}
