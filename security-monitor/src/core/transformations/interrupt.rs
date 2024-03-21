// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialHart;

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
    vsie: usize,
}

impl EnabledInterrupts {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let vsie = confidential_hart.csrs().vsie.read();
        Self { vsie }
    }

    pub fn new(vsie: usize) -> Self {
        Self { vsie }
    }

    pub fn vsie(&self) -> usize {
        self.vsie
    }
}

pub struct InjectedInterrupts {
    hvip: usize,
}

impl InjectedInterrupts {
    pub fn new(hvip: usize) -> Self {
        Self { hvip }
    }

    pub fn hvip(&self) -> usize {
        self.hvip
    }
}
