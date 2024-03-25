// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::transformations::{
    ExposeToConfidentialVm, ExposeToHypervisor, PendingRequest, SbiRequest, SbiResult, SharePageRequest, SharePageResult,
    UnsharePageRequest,
};

/// Handles a request from the confidential VM about creating a shared page.
///
/// Control flows to the hypervisor when the sharing of the given `guest physical address` is allowed. The hypervisor is requested to
/// allocate a page of non-confidential memory and return back the `host physical address` of this page. Control flows back to the
/// confidential hart if the request was invalid, e.g., the `guest physical address` was not correct.
pub fn request_shared_page(confidential_flow: ConfidentialFlow) -> ! {
    let share_page_request = SharePageRequest::from_confidential_hart(confidential_flow.confidential_hart());
    let sbi_request = SbiRequest::kvm_ace_page_in(share_page_request.confidential_vm_physical_address().usize());

    confidential_flow
        .set_pending_request(PendingRequest::SharePage(share_page_request))
        .into_non_confidential_flow()
        .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request))
}

/// Handles a response from the hypervisor about the creation of a shared page.
///
/// Control always flows to the confidential VM.
pub fn share_page(confidential_flow: ConfidentialFlow, request: SharePageRequest) -> ! {
    let share_page_result = SharePageResult::from_hypervisor_hart(confidential_flow.hypervisor_hart());
    if share_page_result.is_error() {
        // Hypervisor returned an error informing that it could not allocate shared pages. Expose this information the
        // confidential VM.
        let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::failure(share_page_result.response_code()));
        confidential_flow.exit_to_confidential_hart(transformation);
    }

    // Security: check that the start address is located in the non-confidential memory
    let hypervisor_address = match NonConfidentialMemoryAddress::new(share_page_result.hypervisor_page_address() as *mut usize) {
        Ok(v) => v,
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    };

    let transformation = ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
        confidential_vm.map_shared_page(hypervisor_address, request.page_size(), *request.confidential_vm_physical_address())
    })
    .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_hart(transformation)
}

/// Handles a request from the confidential VM to unshare a page that was previously shared with the hypervisor.
pub fn unshare_page(confidential_flow: ConfidentialFlow) -> ! {
    let unshare_page_request = UnsharePageRequest::from_confidential_hart(confidential_flow.confidential_hart());

    let transformation = ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
        confidential_vm.unmap_shared_page(unshare_page_request.address())
    })
    .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_hart(transformation)
}
