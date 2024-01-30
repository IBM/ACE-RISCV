// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::ResumeRequest;
use crate::non_confidential_flow::NonConfidentialFlow;

/// Resume handler is called by the hypervisor to resume the confidential VM execution.
pub fn handle(resume_request: ResumeRequest, non_confidential_flow: NonConfidentialFlow) -> ! {
    let (non_confidential_flow, error) = non_confidential_flow.into_confidential_flow(resume_request);
    // Failure of transition into confidential flow indicates an error in the hypervisor because the hypervisor tried to
    // schedule an invalid confidential VM, an invalid confidential hart, or a confidential hart that is already
    // running on another physical hart.
    non_confidential_flow.exit_to_hypervisor(error.into_non_confidential_transformation())
}
