// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialVmId, HardwareHart};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiSrstSystemReset {
    initiating_confidential_hart_id: usize,
}

impl SbiSrstSystemReset {
    pub fn new(initiating_confidential_hart_id: usize) -> Self {
        Self { initiating_confidential_hart_id }
    }

    pub fn initiating_confidential_hart_id(&self) -> usize {
        self.initiating_confidential_hart_id
    }
}

#[derive(PartialEq)]
pub struct TerminateRequest {
    confidential_vm_id: ConfidentialVmId,
}

impl TerminateRequest {
    pub fn from_hardware_hart(hardware_hart: &HardwareHart) -> Self {
        // Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GRPs). GRPs
        // might carry SBI- or MMIO-related reponses, so using GRPs would destroy the communication between the hypervisor and confidential
        // VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V NACL extension that solves these problems by
        // using shared memory region in which the SBI- and MMIO-related information is transfered.
        let confidential_vm_id = hardware_hart.csrs().vstvec.read();
        Self { confidential_vm_id: ConfidentialVmId::new(confidential_vm_id) }
    }

    pub fn confidential_vm_id(&self) -> ConfidentialVmId {
        self.confidential_vm_id
    }
}
