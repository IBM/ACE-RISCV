// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ControlData, PendingRequest};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStart {
    confidential_hart_id: usize,
    start_address: usize,
    opaque: usize,
}

impl SbiHsmHartStart {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            confidential_hart_id: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            start_address: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
            opaque: confidential_hart.gprs().read(GeneralPurposeRegister::a2),
        }
    }

    /// Requests to start a remote confidential hart. This is an implementation of the HartStart function from the HSM extension of SBI.
    ///
    /// This call is triggered by a confidential hart that wants to start another confidential hart. Error is returned to
    /// the caller if the targetted confidential hart is not in the stopped state or it does not exist. The security monitor
    /// moves targetted confidential harts into `StartPending` state and informs then the hypervisor that these harts are
    /// runnable. Once the hypervisor schedules such a confidential hart for execution, the confidential hart will change
    /// the state to `Started`.
    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let confidential_hart_id = self.confidential_hart_id;
        // We expect the confidential hart to be inside the control data (not assigned to a hardware hart), otherwise there is no need to
        // start this confidential hart.
        match ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
            confidential_vm.start_confidential_hart(self)
        }) {
            Ok(_) => confidential_flow
                .set_pending_request(PendingRequest::SbiRequest())
                .into_non_confidential_flow()
                .declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_start(
                    confidential_hart_id,
                ))),
            Err(error) => {
                // starting a confidential hart might fail if the incoming request is invalid. For example, the confidential
                // hart id does not exist or is the same as the one currently assigned to the hardware hart. In such cases,
                // return an error to the calling confidential hart.
                confidential_flow.apply_and_exit_to_confidential_hart(error.into_confidential_transformation())
            }
        }
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn opaque(&self) -> usize {
        self.opaque
    }
}
