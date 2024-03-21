// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};

#[derive(PartialEq)]
pub struct MmioLoadPending {
    instruction_length: usize,
    result_gpr: GeneralPurposeRegister,
}

impl MmioLoadPending {
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

#[derive(PartialEq)]
pub struct MmioStorePending {
    instruction_length: usize,
}

impl MmioStorePending {
    pub fn new(instruction_length: usize) -> Self {
        Self { instruction_length }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
