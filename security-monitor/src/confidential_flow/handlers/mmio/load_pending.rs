// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;

#[derive(PartialEq)]
pub struct MmioLoadPending {
    instruction_length: usize,
    gpr_with_load_result: GeneralPurposeRegister,
}

impl MmioLoadPending {
    pub fn new(instruction_length: usize, gpr_with_load_result: GeneralPurposeRegister) -> Self {
        Self { instruction_length, gpr_with_load_result }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }

    pub fn gpr_with_load_result(&self) -> GeneralPurposeRegister {
        self.gpr_with_load_result
    }
}
