// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{
    ExposeToHypervisor, PendingRequest, SbiRequest, SharePageRequest,
};
use crate::error::Error;

pub fn handle(
    share_page_request: Result<(SharePageRequest, SbiRequest), Error>,
    confidential_flow: ConfidentialFlow,
) -> ! {
    match share_page_request {
        Ok((request, sbi_request)) => {
            debug!(
                "Confidential VM[id={:?}] requested a shared page mapped to {:x}",
                confidential_flow.confidential_vm_id(),
                &request.confidential_vm_virtual_address().usize()
            );
            confidential_flow
                .set_pending_request(PendingRequest::SharePage(request))
                .into_non_confidential_flow()
                .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request))
        }
        Err(error) => {
            confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation())
        }
    }
}
