// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::ResumeRequest;
use crate::non_confidential_flow::NonConfidentialFlow;

/// Resume handler is called by the hypervisor to resume the confidential VM
/// execution.
pub fn handle(resume_request: ResumeRequest, non_confidential_flow: NonConfidentialFlow) -> ! {
    match non_confidential_flow.into_confidential_flow(resume_request) {
        Ok(confidential_flow) => confidential_flow.finish_request(),
        Err((non_confidential_flow, e)) => {
            non_confidential_flow.exit_to_hypervisor(e.into_non_confidential_transformation())
        }
    }
}
