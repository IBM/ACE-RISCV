// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToConfidentialVm, SbiHsmHartStatus, SbiResult};

/// Returns the lifecycle state of the confidential hart as defined in the HART get status (FID #2) function of the SBI's HSM extension.
pub fn handle(request: SbiHsmHartStatus, confidential_flow: ConfidentialFlow) -> ! {
    let transformation = ControlData::try_confidential_vm(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
        confidential_vm.confidential_hart_lifecycle_state(request.confidential_hart_id)
    })
    .and_then(|lifecycle_state| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(lifecycle_state.sbi_code()))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_hart(transformation)
}
