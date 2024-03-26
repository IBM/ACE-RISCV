// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::smp::SbiRequest;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::{DeclassifyToHypervisor, ExposeToHypervisor};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStop {}

impl SbiHsmHartStop {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    /// Stops the confidential hart as defined in the HSM extension of SBI. Error is returned to the confidential hart if
    /// the security monitor cannot stop it, for example, because it is not in the started state.
    ///
    /// The request to stop the confidential hart comes from the confidential hart itself. The security monitor stops the
    /// hart and informs the hypervisor that the hart has been stopped. The hypervisor should not resume execution of a
    /// stopped confidential hart. Only another confidential hart of the confidential VM can start the confidential hart.
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.stop_confidential_hart() {
            Ok(_) => confidential_flow
                .into_non_confidential_flow(DeclassifyToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_stop()))
                .exit_to_hypervisor(ExposeToHypervisor::Resume()),
            Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
        }
    }
}
