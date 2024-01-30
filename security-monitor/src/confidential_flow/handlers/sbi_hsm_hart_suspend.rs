// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, SbiHsmHartSuspend, SbiRequest};

/// Suspends a confidential hart that made this request. This is an implementation of the HartSuspend function from the
/// HSM extension of SBI.
///
/// The request to suspend the confidential hart comes frmo the confidential hart itself. The security monitor suspends
/// the confidential hart and informs about it the hypervisor. This functions returns an error to the calling
/// confidential hart if this confidential hart cannot be suspended, for example, because it is not in the started
/// state.
pub fn handle(request: SbiHsmHartSuspend, mut confidential_flow: ConfidentialFlow) -> ! {
    match confidential_flow.suspend_confidential_hart(request) {
        Ok(_) => confidential_flow
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_suspend())),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}
