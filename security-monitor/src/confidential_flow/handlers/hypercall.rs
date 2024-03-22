// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToConfidentialVm, ExposeToHypervisor, PendingRequest, SbiRequest, SbiResult};

/// Handles a hypercall from a confidential hart to hypervisor.
pub fn make_sbi_call(confidential_flow: ConfidentialFlow) -> ! {
    let sbi_request = SbiRequest::from_confidential_hart(confidential_flow.confidential_hart());
    confidential_flow
        .set_pending_request(PendingRequest::SbiRequest())
        .into_non_confidential_flow()
        .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(sbi_request))
}

/// Handles a response to the hypercall. This response comes from the hypervisor and carries a result of a hypercall
/// requested by the confidential hart.
pub fn process_sbi_response(confidential_flow: ConfidentialFlow) -> ! {
    let hypercall_result = SbiResult::from_hypervisor_hart(&confidential_flow.hardware_hart());
    let transformation = ExposeToConfidentialVm::SbiResult(hypercall_result);
    confidential_flow.exit_to_confidential_hart(transformation)
}
