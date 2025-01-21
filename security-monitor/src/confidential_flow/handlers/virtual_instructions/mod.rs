// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::riscv::specification::WFI_INSTRUCTION;
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::non_confidential_flow::DeclassifyToHypervisor;

/// Handles virtual instruction trap that occured during execution of the confidential hart.
pub struct VirtualInstruction {
    instruction: usize,
    instruction_length: usize,
}

impl VirtualInstruction {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        // According to the RISC-V privilege spec, mtval should store virtual instruction
        let instruction = confidential_hart.csrs().mtval.read();
        let instruction_length = riscv_decode::instruction_length(instruction as u16);
        Self { instruction, instruction_length }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.confidential_hart_mut().csrs_mut().mepc.add(self.instruction_length);

        // let transformation = if self.instruction == WFI_INSTRUCTION {
        //     ApplyToConfidentialHart::VirtualInstruction(self)
        // } else {
        //     // TODO: add support for some CSR manipulation
        //     // TODO: for not supported instructions, inject illegal instruction exception to the guest
        //     panic!("Not supported virtual instruction: {:x}", self.instruction);
        // };
        confidential_flow.into_non_confidential_flow().declassify_and_exit_to_hypervisor(DeclassifyToHypervisor::VirtualInstruction(self))
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // confidential_hart.csrs_mut().mepc.add(self.instruction_length);
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        use crate::confidential_flow::handlers::sbi::SbiResponse;
        use crate::core::architecture::specification::{MIE_SSIP_MASK, SCAUSE_INTERRUPT_MASK};
        hypervisor_hart.csrs_mut().scause.write(MIE_SSIP_MASK | SCAUSE_INTERRUPT_MASK);
        SbiResponse::success().declassify_to_hypervisor_hart(hypervisor_hart);
    }
}
