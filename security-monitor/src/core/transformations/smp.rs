// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStart {
    confidential_hart_id: usize,
    start_address: usize,
    opaque: usize,
}

impl SbiHsmHartStart {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let confidential_hart_id = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let opaque = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        Self { confidential_hart_id, start_address, opaque }
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn opaque(&self) -> usize {
        self.opaque
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartSuspend {
    suspend_type: usize,
    resume_address: usize,
    opaque: usize,
}

impl SbiHsmHartSuspend {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let suspend_type = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let resume_address = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let opaque = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        Self { suspend_type, resume_address, opaque }
    }

    pub fn suspend_type(&self) -> usize {
        self.suspend_type
    }

    pub fn resume_address(&self) -> usize {
        self.resume_address
    }

    pub fn opaque(&self) -> usize {
        self.opaque
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiHsmHartStatus {
    confidential_hart_id: usize,
}

impl SbiHsmHartStatus {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let confidential_hart_id = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        Self { confidential_hart_id }
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_id
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiIpi {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiIpi {
    pub fn new(hart_mask: usize, hart_mask_base: usize) -> Self {
        Self { hart_mask, hart_mask_base }
    }

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { hart_mask, hart_mask_base }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // IPI exposes itself as supervisor-level software interrupt.
        confidential_hart.confidential_hart_state_mut().csrs_mut().vsip.enable_bit_on_saved_value(crate::core::architecture::MIE_VSSIP);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        // according to SBI documentation all harts are selected when the mask_base is of its maximum value
        match self.hart_mask_base == usize::MAX {
            true => true,
            false => hart_id
                .checked_sub(self.hart_mask_base)
                .filter(|id| *id < usize::BITS as usize)
                .is_some_and(|id| self.hart_mask & (1 << id) != 0),
        }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteFenceI {
    ipi: SbiIpi,
}

impl SbiRemoteFenceI {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { ipi: SbiIpi::from_confidential_hart(confidential_hart) }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        crate::core::architecture::fence_i();
        self.ipi.declassify_to_confidential_hart(confidential_hart);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVma {
    ipi: SbiIpi,
    start_address: usize,
    size: usize,
}

impl SbiRemoteSfenceVma {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        Self { ipi, start_address, size }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_vvma();
        self.ipi.declassify_to_confidential_hart(confidential_hart);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVmaAsid {
    ipi: SbiIpi,
    start_address: usize,
    size: usize,
    asid: usize,
}

impl SbiRemoteSfenceVmaAsid {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        let asid = confidential_hart.gprs().read(GeneralPurposeRegister::a4);
        Self { ipi, start_address, size, asid }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_vvma();
        self.ipi.declassify_to_confidential_hart(confidential_hart);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteHfenceGvmaVmid {
    ipi: SbiIpi,
    start_address: usize,
    size: PageSize,
    vmid: ConfidentialVmId,
}

impl SbiRemoteHfenceGvmaVmid {
    pub fn new(
        hart_mask: usize, hart_mask_base: usize, start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId,
    ) -> Self {
        Self { ipi: SbiIpi::new(hart_mask, hart_mask_base), start_address: start_address.usize(), size, vmid }
    }

    pub fn all_harts(start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId) -> Self {
        Self::new(usize::MAX, usize::MAX, start_address, size, vmid)
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_gvma();
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
