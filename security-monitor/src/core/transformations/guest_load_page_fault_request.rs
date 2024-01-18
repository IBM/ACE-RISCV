// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::arch::GpRegister;

#[derive(PartialEq)]
pub struct GuestLoadPageFaultRequest {
    instruction_length: usize,
    result_gpr: GpRegister,
}

impl GuestLoadPageFaultRequest {
    pub fn new(instruction_length: usize, result_gpr: GpRegister) -> Self {
        Self { instruction_length, result_gpr }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }

    pub fn result_gpr(&self) -> GpRegister {
        self.result_gpr
    }
}
