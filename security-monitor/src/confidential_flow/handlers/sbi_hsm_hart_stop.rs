// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, SbiRequest};

/// Stops the confidential hart as defined in the HSM extension of SBI. Error is returned to the confidential hart if
/// the security monitor cannot stop it, for example, because it is not in the started state.
///
/// The request to stop the confidential hart comes from the confidential hart itself. The security monitor stops the
/// hart and informs the hypervisor that the hart has been stopped. The hypervisor should not resume execution of a
/// stopped confidential hart. Only another confidential hart of the confidential VM can start the confidential hart.
pub fn handle(mut confidential_flow: ConfidentialFlow) -> ! {
    match confidential_flow.stop_confidential_hart() {
        Ok(_) => confidential_flow
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_stop())),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}
