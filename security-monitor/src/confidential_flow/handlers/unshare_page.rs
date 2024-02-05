// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult, UnsharePageRequest};
use crate::error::Error;

/// Handles a request from the confidential VM to unshare a page that was previously shared with the hypervisor.
pub fn handle(request: Result<UnsharePageRequest, Error>, confidential_flow: ConfidentialFlow) -> ! {
    let transformation = match request {
        Ok(unshare_page_request) => ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.memory_protector_mut().unmap_shared_page(unshare_page_request.confidential_vm_virtual_address())
        })
        .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
        .unwrap_or_else(|error| error.into_confidential_transformation()),
        Err(error) => error.into_confidential_transformation(),
    };

    confidential_flow.exit_to_confidential_hart(transformation)
}
