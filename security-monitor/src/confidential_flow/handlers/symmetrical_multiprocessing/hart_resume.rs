// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;

/// Suspends a confidential hart that made this request. This is an implementation of the HartSuspend function from the
/// HSM extension of SBI.
///
/// The request to suspend the confidential hart comes from the confidential hart itself. The security monitor suspends
/// the confidential hart and informs the hypervisor. This functions returns an error to the calling
/// confidential hart if this confidential hart cannot be suspended, for example, because it is not in the started
/// state.
pub struct SbiHsmHartResume {
    _suspend_type: usize,
    resume_address: usize,
    opaque: usize,
}

impl SbiHsmHartResume {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            _suspend_type: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            resume_address: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
            opaque: confidential_hart.gprs().read(GeneralPurposeRegister::a2),
        }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.resume_confidential_hart(self.resume_address, self.opaque) {
            Ok(_) => confidential_flow.resume_confidential_hart_execution(),
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }
}
