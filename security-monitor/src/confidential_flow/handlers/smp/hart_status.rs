// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::SbiResult;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ControlData};
use crate::core::transformations::ExposeToConfidentialVm;

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStatus {
    confidential_hart_id: usize,
}

impl SbiHsmHartStatus {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let confidential_hart_id = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        Self { confidential_hart_id }
    }

    /// Returns the lifecycle state of the confidential hart as defined in the HART get status (FID #2) function of the SBI's HSM extension.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ControlData::try_confidential_vm(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
            confidential_vm.confidential_hart_lifecycle_state(self.confidential_hart_id)
        })
        .and_then(|lifecycle_state| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(lifecycle_state.sbi_code()))))
        .unwrap_or_else(|error| error.into_confidential_transformation());

        confidential_flow.exit_to_confidential_hart(transformation)
    }
}
