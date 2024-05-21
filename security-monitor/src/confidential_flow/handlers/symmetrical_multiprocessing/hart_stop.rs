// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::{SbiRequest, SbiResponse};
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::supervisor_binary_interface::HsmExtension;
use crate::core::control_data::ConfidentialHart;
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles a request to stops the confidential hart as defined in the HSM extension of SBI. Error is returned to the confidential hart if
/// the security monitor cannot stop it, for example, because it is not in the started state.
///
/// The request to stop the confidential hart comes from the confidential hart itself. The security monitor stops the
/// hart and informs the hypervisor that the hart has been stopped. The hypervisor should not resume execution of a
/// stopped confidential hart. Only another confidential hart of the confidential VM can start the confidential hart.
pub struct SbiHsmHartStop {}

impl SbiHsmHartStop {
    pub fn from_confidential_hart(_confidential_hart: &ConfidentialHart) -> Self {
        Self {}
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.stop_confidential_hart() {
            Ok(_) => confidential_flow
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(self.kvm_hsm_hart_stop())),
            Err(error) => {
                let transformation = ApplyToConfidentialHart::SbiResponse(SbiResponse::failure(error.code()));
                confidential_flow.apply_and_exit_to_confidential_hart(transformation)
            }
        }
    }

    pub fn kvm_hsm_hart_stop(&self) -> SbiRequest {
        SbiRequest::new(HsmExtension::EXTID, HsmExtension::HART_STOP_FID, 0, 0)
    }
}
