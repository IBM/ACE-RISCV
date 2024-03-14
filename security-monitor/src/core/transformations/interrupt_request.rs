// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::CSR;

pub struct InterruptRequest {
    code: usize,
}

impl InterruptRequest {
    pub fn new(code: usize) -> Self {
        Self { code }
    }

    pub fn code(&self) -> usize {
        self.code
    }
}

pub struct EnabledInterrupts {
    pub vsie: usize,
}

impl EnabledInterrupts {
    pub fn new() -> Self {
        Self { vsie: CSR.vsie.read() }
    }
}

pub struct InjectedInterrupts {
    pub hvip: usize,
}

impl InjectedInterrupts {
    pub fn new() -> Self {
        Self { hvip: CSR.hvip.read() }
    }
}
