// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::SbiRequest;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::{DeclassifyToHypervisor, ExposeToHypervisor};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartSuspend {
    suspend_type: usize,
    resume_address: usize,
    opaque: usize,
}

impl SbiHsmHartSuspend {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let suspend_type = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let resume_address = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let opaque = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        Self { suspend_type, resume_address, opaque }
    }

    /// Suspends a confidential hart that made this request. This is an implementation of the HartSuspend function from the
    /// HSM extension of SBI.
    ///
    /// The request to suspend the confidential hart comes frmo the confidential hart itself. The security monitor suspends
    /// the confidential hart and informs about it the hypervisor. This functions returns an error to the calling
    /// confidential hart if this confidential hart cannot be suspended, for example, because it is not in the started
    /// state.
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.suspend_confidential_hart(self) {
            Ok(_) => confidential_flow
                .into_non_confidential_flow(DeclassifyToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_suspend()))
                .exit_to_hypervisor(ExposeToHypervisor::Resume()),
            Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
        }
    }
}
