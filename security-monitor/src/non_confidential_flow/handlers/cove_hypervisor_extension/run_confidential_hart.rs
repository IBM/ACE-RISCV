// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::DeclassifyToConfidentialVm;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, HypervisorHart};
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct RunConfidentialHart {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
    allowed_external_interrupts: usize,
    stimecmp: usize,
    hvip: usize,
}

impl RunConfidentialHart {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)),
            confidential_hart_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            allowed_external_interrupts: 0,
            stimecmp: hypervisor_hart.csrs().stimecmp.read(),
            hvip: hypervisor_hart.csrs().hvip.read(),
        }
    }

    pub fn handle(mut self, non_confidential_flow: NonConfidentialFlow) -> ! {
        match non_confidential_flow.into_confidential_flow(self.confidential_vm_id, self.confidential_hart_id) {
            Ok((allowed_external_interrupts, confidential_flow)) => {
                self.allowed_external_interrupts = allowed_external_interrupts;
                confidential_flow
                    .declassify_to_confidential_hart(DeclassifyToConfidentialVm::Resume(self))
                    .resume_confidential_hart_execution()
            }
            Err((non_confidential_flow, error)) => {
                // Properly implemented hypervisor should never let us enter this code. Entering this code means that the
                // transition into confidential flow failed. This might indicate an error in the hypervisor implementation
                // because the hypervisor tried to schedule an invalid confidential VM, an invalid confidential hart, or a
                // confidential hart that is already running on another physical hart.
                let transformation = ApplyToHypervisorHart::SbiResponse(SbiResponse::error(error));
                non_confidential_flow.apply_and_exit_to_hypervisor(transformation)
            }
        }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // Guard against stepping attacks by adding random delay to the timer
        let delay = 10; // TODO: generate random number

        // We write directly to the CSR because we are after the heavy context switch
        confidential_hart.csrs_mut().stimecmp.write(self.stimecmp + delay);

        // Inject external interrupts
        confidential_hart.csrs_mut().hvip.save_value_in_main_memory(self.hvip & self.allowed_external_interrupts);
    }
}
