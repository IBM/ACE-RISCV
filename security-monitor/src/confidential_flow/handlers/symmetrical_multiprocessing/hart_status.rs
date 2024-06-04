// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ControlDataStorage};

/// Handles the request from a confidential hart to learn about the lifecycle state of another confidential hart as defined in the HART get
/// status (FID #2) function of the SBI's HSM extension.
pub struct SbiHsmHartStatus {
    confidential_hart_id: usize,
}

impl SbiHsmHartStatus {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { confidential_hart_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0) }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ControlDataStorage::try_confidential_vm(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
            confidential_vm.confidential_hart_lifecycle_state(self.confidential_hart_id)
        })
        .and_then(|lifecycle_state| Ok(SbiResponse::success_with_code(lifecycle_state.sbi_code())))
        .unwrap_or_else(|error| SbiResponse::error(error));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}
