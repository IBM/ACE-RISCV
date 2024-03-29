// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq)]
pub struct VirtualInstructionRequest {
    pub instruction: usize,
    pub instruction_length: usize,
}

#[derive(PartialEq)]
pub struct VirtualInstructionResult {
    pub instruction_length: usize,
}

impl VirtualInstructionResult {
    pub fn new(instruction_length: usize) -> Self {
        Self { instruction_length }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
