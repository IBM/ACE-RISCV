// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToHypervisor, ResumeRequest, SbiRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

/// Resume handler is called by the hypervisor to resume the confidential VM execution.
pub fn handle(non_confidential_flow: NonConfidentialFlow) -> ! {
    let request = ResumeRequest::from_hypervisor_hart(non_confidential_flow.hypervisor_hart());
    let (non_confidential_flow, _error) = non_confidential_flow.into_confidential_flow(request);

    // Properly implemented hypervisor should never let us enter this code. Entering this code means that the transition into confidential
    // flow failed. This might indicate an error in the hypervisor implementation because the hypervisor tried to schedule an invalid
    // confidential VM, an invalid confidential hart, or a confidential hart that is already running on another physical hart. Let's
    // keep informing the hypervisor that the confidential VM is shutdown regardless of what the real reason is.
    let transformation = ExposeToHypervisor::SbiRequest(SbiRequest::kvm_srst_system_reset());
    non_confidential_flow.exit_to_hypervisor(transformation)
}
