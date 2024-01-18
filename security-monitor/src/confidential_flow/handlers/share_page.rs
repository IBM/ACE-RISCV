// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, PendingRequest, SbiRequest, SharePageRequest};
use crate::error::Error;

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows:
/// - to the hypervisor
/// - back to the confidential VM on error
pub fn handle(request: Result<(SharePageRequest, SbiRequest), Error>, confidential_flow: ConfidentialFlow) -> ! {
    match request {
        Ok((share_page_request, sbi_request)) => {
            debug!(
                "Confidential VM[confidential_vm_id={:?}] requested a shared page mapped to address [guest_physical_address={:?}]",
                confidential_flow.confidential_vm_id(),
                share_page_request.confidential_vm_virtual_address()
            );
            confidential_flow
                .set_pending_request(PendingRequest::SharePage(share_page_request))
                .into_non_confidential_flow()
                .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request))
        }
        Err(error) => confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation()),
    }
}
