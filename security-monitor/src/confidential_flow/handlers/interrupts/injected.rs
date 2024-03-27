// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct InjectedInterrupts {
    hvip: usize,
}

impl InjectedInterrupts {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { hvip: hypervisor_hart.csrs().hvip.read() }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.csrs_mut().hvip.save_value(self.hvip);
    }
}
