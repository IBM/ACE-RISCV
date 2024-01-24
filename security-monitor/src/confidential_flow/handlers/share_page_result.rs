// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::page_allocator::SharedPage;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult, SharePageRequest, SharePageResult};

/// Handles a response from the hypervisor about the creation of a shared page.
///
/// Control always flows to the confidential VM.
pub fn handle(share_page_result: SharePageResult, confidential_flow: ConfidentialFlow, request: SharePageRequest) -> ! {
    let confidential_vm_id = confidential_flow.confidential_vm_id();

    if share_page_result.is_error() {
        // hypervisor returned an error informing that it could not allocate shared pages. Expose this information the
        // confidential VM.
        let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::failure(share_page_result.response_code()));
        confidential_flow.exit_to_confidential_vm(transformation);
    }

    let shared_page = match SharedPage::new(share_page_result.hypervisor_page_address(), request) {
        Ok(v) => v,
        Err(error) => confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation()),
    };

    debug!(
        "Hypervisor shared a page with the confidential VM [{:?}] at address [physical address=0x{:x}]",
        confidential_vm_id,
        share_page_result.hypervisor_page_address()
    );

    let transformation = ControlData::try_confidential_vm_mut(confidential_vm_id, |mut confidential_vm| {
        confidential_vm.memory_protector_mut().map_shared_page(shared_page)
    })
    .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_vm(transformation)
}
