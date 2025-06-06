// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::{CSR_HVIP, CSR_VSIE, CSR_VSTIMECMP};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct ExposeEnabledInterrupts {
    vsie: usize,
    vstimecmp: usize,
}

impl ExposeEnabledInterrupts {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { vsie: confidential_hart.csrs().vsie.read(), vstimecmp: confidential_hart.sstc().vstimecmp.read() }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.shared_memory_mut().write_csr(CSR_VSIE.into(), self.vsie);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HVIP.into(), 0);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_VSTIMECMP.into(), self.vstimecmp);
    }
}
