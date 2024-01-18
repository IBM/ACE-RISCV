// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::arch::GpRegister;

pub struct MmioStoreRequest {
    code: usize,
    stval: usize,
    htval: usize,
    instruction: usize,
    gpr: GpRegister,
    gpr_value: usize,
}

impl MmioStoreRequest {
    pub fn new(code: usize, stval: usize, htval: usize, instruction: usize, gpr: GpRegister, gpr_value: usize) -> Self {
        Self { code, stval, htval, instruction, gpr, gpr_value: gpr_value }
    }

    pub fn code(&self) -> usize {
        self.code
    }

    pub fn stval(&self) -> usize {
        self.stval
    }

    pub fn htval(&self) -> usize {
        self.htval
    }

    pub fn instruction(&self) -> usize {
        self.instruction
    }

    pub fn gpr(&self) -> GpRegister {
        self.gpr
    }

    pub fn gpr_value(&self) -> usize {
        self.gpr_value
    }
}
