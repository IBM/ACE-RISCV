// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::memory_tracker::SharedPage;
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult, SharePageRequest, SharePageResult};

pub fn handle(share_page_result: SharePageResult, confidential_flow: ConfidentialFlow, request: SharePageRequest) -> ! {
    if share_page_result.is_error() {
        // hypervisor returned an error informing that it could not allocate shared
        // pages let's inform the confidential VM about it.
        let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::failure(share_page_result.response_code()));
        confidential_flow.exit_to_confidential_vm(transformation);
    }

    let shared_page = match SharedPage::new(share_page_result.hypervisor_page_address(), request) {
        Ok(v) => v,
        Err(error) => confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation()),
    };

    debug!(
        "Hypervisor shared pages with confidential VM at hv_paddr=0x{:x}",
        share_page_result.hypervisor_page_address()
    );

    let confidential_vm_id = confidential_flow.confidential_vm_id();
    let transformation = ControlData::try_confidential_vm_mut(confidential_vm_id, |mut cvm| {
        cvm.memory_protector_mut().map_shared_page(shared_page)
    })
    .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_vm(transformation)
}
