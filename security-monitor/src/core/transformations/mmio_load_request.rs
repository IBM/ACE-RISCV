// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub struct MmioLoadRequest {
    code: usize,
    stval: usize,
    htval: usize,
    instruction: usize,
}

impl MmioLoadRequest {
    pub fn new(code: usize, stval: usize, htval: usize, instruction: usize) -> Self {
        Self { code, stval, htval, instruction }
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
}
