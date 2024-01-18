// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::InterHartRequest;

/// Injects an InterHartRequest to confidential harts specified as part of the request.
pub fn handle(inter_hart_request: InterHartRequest, confidential_flow: ConfidentialFlow) -> ! {
    use crate::core::control_data::ControlData;
    use crate::core::transformations::{ExposeToConfidentialVm, SbiResult};

    let confidential_vm_id = confidential_flow.confidential_vm_id();
    let transformation = ControlData::try_confidential_vm_mut(confidential_vm_id, |ref mut confidential_vm| {
        confidential_vm.add_inter_hart_request(inter_hart_request.clone())
    })
    .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_vm(transformation)
}
