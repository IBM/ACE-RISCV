// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct InterruptRequest {
    code: usize,
}

impl InterruptRequest {
    pub fn new(code: usize) -> Self {
        Self { code }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        use crate::core::architecture::SCAUSE_INTERRUPT_MASK;
        hypervisor_hart.csrs_mut().scause.set(self.code | SCAUSE_INTERRUPT_MASK);
        hypervisor_hart.apply_trap(false);
    }
}

pub struct EnabledInterrupts {
    vsie: usize,
}

impl EnabledInterrupts {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { vsie: confidential_hart.confidential_hart_state().csrs().vsie.read() }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().vsie.set(self.vsie);
    }
}

pub struct InjectedInterrupts {
    hvip: usize,
}

impl InjectedInterrupts {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { hvip: hypervisor_hart.csrs().hvip.read() }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.confidential_hart_state_mut().csrs_mut().hvip.save_value(self.hvip());
    }

    pub fn hvip(&self) -> usize {
        self.hvip
    }
}
