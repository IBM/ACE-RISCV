// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;

#[derive(PartialEq)]
pub struct GuestLoadPageFaultRequest {
    instruction_length: usize,
    result_gpr: GeneralPurposeRegister,
}

impl GuestLoadPageFaultRequest {
    pub fn new(instruction_length: usize, result_gpr: GeneralPurposeRegister) -> Self {
        Self { instruction_length, result_gpr }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }

    pub fn result_gpr(&self) -> GeneralPurposeRegister {
        self.result_gpr
    }
}
