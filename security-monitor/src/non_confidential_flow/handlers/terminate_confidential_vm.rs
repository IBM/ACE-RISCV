// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::core::control_data::{ConfidentialVmId, ControlData, HypervisorHart};
use crate::non_confidential_flow::{ApplyToHypervisor, NonConfidentialFlow};

#[derive(PartialEq)]
pub struct TerminateRequest {
    confidential_vm_id: ConfidentialVmId,
}

impl TerminateRequest {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        // Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GRPs). GRPs
        // might carry SBI- or MMIO-related reponses, so using GRPs would destroy the communication between the hypervisor and confidential
        // VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V NACL extension that solves these problems by
        // using shared memory region in which the SBI- and MMIO-related information is transfered.
        let confidential_vm_id = hypervisor_hart.csrs().vstvec.read();
        Self { confidential_vm_id: ConfidentialVmId::new(confidential_vm_id) }
    }

    /// The hypervisor command to terminate the confidential VM and remove it from the memory.
    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        non_confidential_flow.hack_restore_original_gprs();
        let transformation = ControlData::remove_confidential_vm(self.confidential_vm_id)
            .and_then(|_| Ok(ApplyToHypervisor::SbiResult(SbiResult::success(0))))
            .unwrap_or_else(|error| error.into_non_confidential_transformation());
        non_confidential_flow.exit_to_hypervisor(transformation)
    }
}
