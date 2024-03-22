// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialHart;

#[derive(PartialEq)]
pub struct VirtualInstructionRequest {
    instruction: usize,
    instruction_length: usize,
}

impl VirtualInstructionRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        // According to the RISC-V privilege spec, mtval should store virtual instruction
        let instruction = confidential_hart.confidential_hart_state().csrs().mtval.read();
        let instruction_length = riscv_decode::instruction_length(instruction as u16);
        Self { instruction, instruction_length }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.confidential_hart_state().csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.confidential_hart_state_mut().csrs_mut().mepc.save_value(new_mepc);
    }

    pub fn instruction(&self) -> usize {
        self.instruction
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
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
        let new_mepc = confidential_hart.confidential_hart_state().csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.confidential_hart_state_mut().csrs_mut().mepc.save_value(new_mepc);
    }
}
