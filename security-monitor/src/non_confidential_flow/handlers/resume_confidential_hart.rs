// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::core::architecture::SrstExtension;
use crate::core::control_data::{ConfidentialVmId, HypervisorHart};
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

/// Handles the hypervisor request to resume execution of a confidential hart.
pub struct ResumeHandler {
    confidential_vm_id: ConfidentialVmId,
    confidential_hart_id: usize,
}

impl ResumeHandler {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        // Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GPRs). GPRs
        // might carry SBI- or MMIO-related reponses, so using GPRs would destroy the communication between the hypervisor and confidential
        // VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V NACL extension that solves these problems by
        // using shared memory region in which the SBI- and MMIO-related information is transfered.
        let confidential_vm_id = hypervisor_hart.csrs().vstvec.read();
        let confidential_hart_id = hypervisor_hart.csrs().vsscratch.read();

        Self { confidential_vm_id: ConfidentialVmId::new(confidential_vm_id), confidential_hart_id }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow.hack_restore_original_gprs();
        match non_confidential_flow.into_confidential_flow(self.confidential_vm_id, self.confidential_hart_id) {
            Ok(confidential_flow) => confidential_flow.resume_confidential_hart_execution(),
            Err((non_confidential_flow, _error)) => {
                // Properly (safety) implemented hypervisor should never let us enter this code. Entering this code means that the
                // transition into confidential flow failed. This might indicate an error in the hypervisor implementation
                // because the hypervisor tried to schedule an invalid confidential VM, an invalid confidential hart, or a
                // confidential hart that is already running on another physical hart. Let's keep informing the hypervisor
                // that the confidential VM is shutdown regardless of what the real reason is.
                let kvm_srst_system_reset = SbiRequest::new(SrstExtension::EXTID, SrstExtension::SYSTEM_RESET_FID, 0, 0, 0, 0, 0, 0);
                non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisor::SbiRequest(kvm_srst_system_reset))
            }
        }
    }
}
