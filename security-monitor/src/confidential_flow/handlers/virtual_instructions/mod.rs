// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::WFI_INSTRUCTION;
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::ExposeToConfidentialVm;

// pub use virtual_instruction::{VirtualInstructionRequest, VirtualInstructionResult};

#[derive(PartialEq)]
pub struct VirtualInstructionRequest {
    instruction: usize,
    instruction_length: usize,
}

impl VirtualInstructionRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        // According to the RISC-V privilege spec, mtval should store virtual instruction
        let instruction = confidential_hart.csrs().mtval.read();
        let instruction_length = riscv_decode::instruction_length(instruction as u16);
        Self { instruction, instruction_length }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = if self.instruction == WFI_INSTRUCTION {
            ExposeToConfidentialVm::VirtualInstructionResult(VirtualInstructionResult::new(self.instruction_length))
        } else {
            // TODO: add support for some CSR manipulation
            // TODO: for not supported instructions, inject illegal instruction exception to the guest
            panic!("Not supported virtual instruction: {:x}", self.instruction);
        };
        confidential_flow.exit_to_confidential_hart(transformation)
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}

#[derive(PartialEq)]
pub struct VirtualInstructionResult {
    instruction_length: usize,
}

impl VirtualInstructionResult {
    pub fn new(instruction_length: usize) -> Self {
        Self { instruction_length }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}
