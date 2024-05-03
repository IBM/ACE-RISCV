// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::CSR_HVIP;
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct InjectInterrupt {
    hvip: usize,
}

impl InjectInterrupt {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { hvip: hypervisor_hart.shared_memory().csr(CSR_HVIP.into()) }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        if self.hvip != 0 {
            debug!("HVIP: {:x}", self.hvip);
        }
        confidential_hart.csrs_mut().hvip.save_value(self.hvip);
    }
}
