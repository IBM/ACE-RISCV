// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::HypervisorHart;
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;

pub struct PromoteToConfidentialVm {
    hart_state: HartArchitecturalState,
}

impl PromoteToConfidentialVm {
    pub fn from_vm_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { hart_state: HartArchitecturalState::from_existing(0, hypervisor_hart.hypervisor_hart_state()) }
    }

    /// Returns the address of the device tree provided as the first argument of the call.
    pub fn fdt_address(&self) -> ConfidentialVmPhysicalAddress {
        ConfidentialVmPhysicalAddress::new(self.hart_state.gprs.read(GeneralPurposeRegister::a0))
    }

    pub fn into(self) -> (ConfidentialVmPhysicalAddress, HartArchitecturalState) {
        (self.fdt_address(), self.hart_state)
    }
}
