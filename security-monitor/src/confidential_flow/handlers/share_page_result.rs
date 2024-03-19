// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::memory_layout::NonConfidentialMemoryAddress;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult, SharePageRequest, SharePageResult};

/// Handles a response from the hypervisor about the creation of a shared page.
///
/// Control always flows to the confidential VM.
pub fn handle(share_page_result: SharePageResult, confidential_flow: ConfidentialFlow, request: SharePageRequest) -> ! {
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
