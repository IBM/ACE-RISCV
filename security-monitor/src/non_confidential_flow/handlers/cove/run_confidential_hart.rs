// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::core::architecture::{GeneralPurposeRegister, SrstExtension};
use crate::core::control_data::{ConfidentialVmId, HypervisorHart};
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct RunConfidentialHart {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
}

impl RunConfidentialHart {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self {
            confidential_vm_id: ConfidentialVmId::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0)),
            confidential_hart_id: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        match non_confidential_flow.into_confidential_flow(self.confidential_vm_id, self.confidential_hart_id) {
            Ok(confidential_flow) => confidential_flow.resume_confidential_hart_execution(),
            Err((non_confidential_flow, error)) => {
                // Properly (safety) implemented hypervisor should never let us enter this code. Entering this code means that the
                // transition into confidential flow failed. This might indicate an error in the hypervisor implementation
                // because the hypervisor tried to schedule an invalid confidential VM, an invalid confidential hart, or a
                // confidential hart that is already running on another physical hart. Let's keep informing the hypervisor
                // that the confidential VM is shutdown regardless of what the real reason is.
                non_confidential_flow.apply_and_exit_to_hypervisor(error.into_non_confidential_transformation())
            }
        }
    }
}
