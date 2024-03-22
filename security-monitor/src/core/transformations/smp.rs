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
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { hart_mask, hart_mask_base }
    }

    pub fn hart_mask(&self) -> usize {
        self.hart_mask
    }

    pub fn hart_mask_base(&self) -> usize {
        self.hart_mask_base
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteFenceI {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiRemoteFenceI {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        Self { hart_mask, hart_mask_base }
    }

    pub fn new(hart_mask: usize, hart_mask_base: usize) -> Self {
        Self { hart_mask, hart_mask_base }
    }

    pub fn hart_mask(&self) -> usize {
        self.hart_mask
    }

    pub fn hart_mask_base(&self) -> usize {
        self.hart_mask_base
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVma {
    hart_mask: usize,
    hart_mask_base: usize,
    start_address: usize,
    size: usize,
}

impl SbiRemoteSfenceVma {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        Self { hart_mask, hart_mask_base, start_address, size }
    }

    pub fn hart_mask(&self) -> usize {
        self.hart_mask
    }

    pub fn hart_mask_base(&self) -> usize {
        self.hart_mask_base
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn size(&self) -> usize {
        self.size
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVmaAsid {
    hart_mask: usize,
    hart_mask_base: usize,
    start_address: usize,
    size: usize,
    asid: usize,
}

impl SbiRemoteSfenceVmaAsid {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let hart_mask = confidential_hart.gprs().read(GeneralPurposeRegister::a0);
        let hart_mask_base = confidential_hart.gprs().read(GeneralPurposeRegister::a1);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        let asid = confidential_hart.gprs().read(GeneralPurposeRegister::a4);
        Self { hart_mask, hart_mask_base, start_address, size, asid }
    }

    pub fn hart_mask(&self) -> usize {
        self.hart_mask
    }

    pub fn hart_mask_base(&self) -> usize {
        self.hart_mask_base
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn asid(&self) -> usize {
        self.asid
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteHfenceGvmaVmid {
    hart_mask: usize,
    hart_mask_base: usize,
    start_address: usize,
    size: usize,
    vmid: usize,
}

impl SbiRemoteHfenceGvmaVmid {
    pub fn new(
        hart_mask: usize, hart_mask_base: usize, start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId,
    ) -> Self {
        Self { hart_mask, hart_mask_base, start_address: start_address.usize(), size: size.in_bytes(), vmid: vmid.usize() }
    }

    pub fn all_harts(start_address: &ConfidentialVmPhysicalAddress, size: PageSize, vmid: ConfidentialVmId) -> Self {
        Self::new(usize::MAX, usize::MAX, start_address, size, vmid)
    }

    pub fn hart_mask(&self) -> usize {
        self.hart_mask
    }

    pub fn hart_mask_base(&self) -> usize {
        self.hart_mask_base
    }

    pub fn start_address(&self) -> usize {
        self.start_address
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn vmid(&self) -> usize {
        self.vmid
    }
}
