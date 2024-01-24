// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::HartLifecycleStateTransition;
use crate::core::transformations::{ExposeToHypervisor, PendingRequest, SbiHsmHartStart, SbiRequest};

/// Starts a confidential hart. This is an implementation of the HartStart function from the HSM extension of SBI.
///
/// This call is triggered by a confidential hart that wants to start another confidential hart. Error is returned to
/// the caller if the targetted confidential hart is not in the stopped state or it does not exist. The security monitor
/// moves targetted confidential harts into `StartPending` state and informs then the hypervisor that these harts are
/// runnable. Once the hypervisor schedules such a confidential hart for execution, the confidential hart will change
/// the state to `Started`.
pub fn handle(request: SbiHsmHartStart, mut confidential_flow: ConfidentialFlow) -> ! {
    let confidential_hart_id = request.confidential_hart_id;
    match confidential_flow.transit_hart_lifecycle(HartLifecycleStateTransition::StoppedToStartPending(request)) {
        Ok(_) => confidential_flow
            .set_pending_request(PendingRequest::SbiHsmHartStart())
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_start(confidential_hart_id))),
        Err(error) => {
            // starting a confidential hart might fail if the incoming request is invalid. For example, the confidential
            // hart id does not exist or is the same as the one currently assigned to the hardware hart. In such cases,
            // return an error to the calling confidential hart.
            confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation());
        }
    }
}
