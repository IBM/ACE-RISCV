// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};
use crate::core::architecture::WFI_INSTRUCTION;
use crate::core::control_data::ConfidentialHart;

#[derive(PartialEq)]
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

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = if self.instruction == WFI_INSTRUCTION {
            ApplyToConfidentialVm::VirtualInstruction(self)
        } else {
            // TODO: add support for some CSR manipulation
            // TODO: for not supported instructions, inject illegal instruction exception to the guest
            panic!("Not supported virtual instruction: {:x}", self.instruction);
        };
        confidential_flow.exit_to_confidential_hart(transformation)
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}
