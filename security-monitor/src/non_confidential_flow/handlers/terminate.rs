// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToHypervisor, SbiResult, TerminateRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

/// The hypervisor command to terminate the confidential VM and remove it from the memory.
pub fn handle(terminate_request: TerminateRequest, non_confidential_flow: NonConfidentialFlow) -> ! {
    let transformation = ControlData::try_write(|control_data| {
        let confidential_vm_id = terminate_request.confidential_vm_id();
        debug!("Terminating the confidential VM[id={:?}]", confidential_vm_id);
        control_data.remove_confidential_vm(confidential_vm_id)
    })
    .and_then(|_| Ok(ExposeToHypervisor::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_non_confidential_transformation());

    non_confidential_flow.exit_to_hypervisor(transformation)
}
