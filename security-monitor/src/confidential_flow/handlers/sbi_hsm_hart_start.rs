// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToHypervisor, InterHartRequest, PendingRequest, SbiHsmHartStart, SbiRequest};

/// Handles HartStart function from the HSM extension of SBI.
pub fn handle(request: SbiHsmHartStart, confidential_flow: ConfidentialFlow) -> ! {
    let confidential_hart_id = request.confidential_hart_id;
    // TODO: we must check the state of the hart and only allow starting a HART that is in the shutdown state
    match ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
        Ok(confidential_vm.add_inter_hart_request(InterHartRequest::SbiHsmHartStart(request)))
    }) {
        Ok(_) => confidential_flow
            .set_pending_request(PendingRequest::SbiRequest())
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_start(confidential_hart_id))),
        Err(error) => {
            confidential_flow.exit_to_confidential_vm(error.into_confidential_transformation());
        }
    }
}
