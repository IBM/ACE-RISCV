// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialVmId;
use crate::core::hart::{GpRegister, HartState};

pub struct SbiRequest {
    extension_id: usize,
    function_id: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
}

impl SbiRequest {
    const KVM_ACE_EXTID: usize = 0x509999;
    const KVM_ACE_REGISTER_FID: usize = 1;
    const KVM_ACE_PAGE_IN_FID: usize = 2;

    pub fn kvm_ace_register(confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize) -> Self {
        Self::new(
            Self::KVM_ACE_EXTID,
            Self::KVM_ACE_REGISTER_FID,
            confidential_vm_id.usize(),
            confidential_hart_id,
            0,
            0,
            0,
            0,
        )
    }

    pub fn kvm_ace_page_in(page_address: usize) -> Self {
        Self::new(Self::KVM_ACE_EXTID, Self::KVM_ACE_PAGE_IN_FID, page_address, 0, 0, 0, 0, 0)
    }

    // only ConfidentialHart or HardwareHart can invoke this function because only they have access to the HartState
    // storing confidential information
    pub fn from_hart_state(hart_state: &HartState) -> Self {
        Self::new(
            hart_state.gpr(GpRegister::a7),
            hart_state.gpr(GpRegister::a6),
            hart_state.gpr(GpRegister::a0),
            hart_state.gpr(GpRegister::a1),
            hart_state.gpr(GpRegister::a2),
            hart_state.gpr(GpRegister::a3),
            hart_state.gpr(GpRegister::a4),
            hart_state.gpr(GpRegister::a5),
        )
    }

    pub fn new(
        extension_id: usize, function_id: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize,
    ) -> Self {
        Self { extension_id, function_id, a0, a1, a2, a3, a4, a5 }
    }

    pub fn extension_id(&self) -> usize {
        self.extension_id
    }

    pub fn function_id(&self) -> usize {
        self.function_id
    }

    pub fn a0(&self) -> usize {
        self.a0
    }

    pub fn a1(&self) -> usize {
        self.a1
    }

    pub fn a2(&self) -> usize {
        self.a2
    }

    pub fn a3(&self) -> usize {
        self.a3
    }

    pub fn a4(&self) -> usize {
        self.a4
    }

    pub fn a5(&self) -> usize {
        self.a5
    }
}
