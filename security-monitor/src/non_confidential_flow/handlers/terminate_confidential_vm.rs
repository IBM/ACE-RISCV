// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToHypervisor, SbiResult, TerminateRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

/// The hypervisor command to terminate the confidential VM and remove it from the memory.
pub fn handle(non_confidential_flow: NonConfidentialFlow) -> ! {
    let request = TerminateRequest::from_hardware_hart(non_confidential_flow.hardware_hart());
    let transformation = ControlData::remove_confidential_vm(request.confidential_vm_id())
        .and_then(|_| Ok(ExposeToHypervisor::SbiResult(SbiResult::success(0))))
        .unwrap_or_else(|error| error.into_non_confidential_transformation());
    non_confidential_flow.exit_to_hypervisor(transformation)
}
