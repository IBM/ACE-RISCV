// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HardwareHart};

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
        Self { vsie: confidential_hart.confidential_hart_state().csrs().vsie.read() }
    }

    pub fn declassify_to_hardware_hart(&self, hardware_hart: &mut HardwareHart) {
        hardware_hart.hypervisor_hart_state_mut().csrs_mut().vsie.set(self.vsie);
    }
}

pub struct InjectedInterrupts {
    hvip: usize,
}

impl InjectedInterrupts {
    pub fn from_hardware_hart(hardware_hart: &HardwareHart) -> Self {
        Self { hvip: hardware_hart.hypervisor_hart_state().csrs().hvip.read() }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.confidential_hart_state_mut().csrs_mut().hvip.save_value(self.hvip());
    }

    pub fn hvip(&self) -> usize {
        self.hvip
    }
}
