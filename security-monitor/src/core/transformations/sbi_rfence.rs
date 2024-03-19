// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::ConfidentialVmId;
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::PageSize;

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteFenceI {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiRemoteFenceI {
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
    pub fn new(hart_mask: usize, hart_mask_base: usize, start_address: usize, size: usize) -> Self {
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
    pub fn new(hart_mask: usize, hart_mask_base: usize, start_address: usize, size: usize, asid: usize) -> Self {
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
