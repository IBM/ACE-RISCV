// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::DeclassifyToConfidentialVm;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, HypervisorHart};
use crate::core::timer_controller::TimerController;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct RunConfidentialHart {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
    allowed_external_interrupts: usize,
    hvip: usize,
}

impl RunConfidentialHart {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)),
            confidential_hart_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            allowed_external_interrupts: 0,
            hvip: hypervisor_hart.csrs().hvip.read(),
        }
    }

    pub fn handle(mut self, non_confidential_flow: NonConfidentialFlow) -> ! {
        match non_confidential_flow.into_confidential_flow(self.confidential_vm_id, self.confidential_hart_id) {
            Ok((allowed_external_interrupts, mut confidential_flow)) => {
                self.allowed_external_interrupts = allowed_external_interrupts;
                TimerController::new(&mut confidential_flow).restore_vs_timer();
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
        confidential_hart.csrs_mut().allowed_external_interrupts = self.allowed_external_interrupts;

        use crate::core::architecture::specification::*;
        let hvip = self.hvip & !(MIE_VSSIP_MASK | MIE_VSTIP_MASK);
        confidential_hart.csrs_mut().hvip.save_value_in_main_memory(hvip);
    }
}
