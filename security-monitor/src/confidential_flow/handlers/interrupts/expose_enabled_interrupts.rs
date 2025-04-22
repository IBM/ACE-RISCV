// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::{CSR_HVIP, CSR_VSIE, CSR_VSTIMECMP};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct ExposeEnabledInterrupts {
    vsie: usize,
    hvip: usize,
    vstimecmp: usize,
}

impl ExposeEnabledInterrupts {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let htimedelta = confidential_hart.csrs().htimedelta;
        Self {
            vsie: confidential_hart.csrs().vsie.read(),
            hvip: confidential_hart.csrs().hvip.read(),
            vstimecmp: confidential_hart.csrs().vstimecmp.and_then(|v| Some(v.wrapping_add(htimedelta))).unwrap_or(usize::MAX),
        }
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.shared_memory_mut().write_csr(CSR_VSIE.into(), self.vsie);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HVIP.into(), self.hvip);
        hypervisor_hart.shared_memory_mut().write_csr(CSR_VSTIMECMP.into(), self.vstimecmp);
    }
}
