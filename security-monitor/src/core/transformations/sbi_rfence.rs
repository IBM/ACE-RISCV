// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteFenceI {
    pub hart_mask: usize,
    pub hart_mask_base: usize,
}

impl SbiRemoteFenceI {
    pub fn new(hart_mask: usize, hart_mask_base: usize) -> Self {
        Self { hart_mask, hart_mask_base }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVma {
    pub hart_mask: usize,
    pub hart_mask_base: usize,
    pub start_address: usize,
    pub size: usize,
}

impl SbiRemoteSfenceVma {
    pub fn new(hart_mask: usize, hart_mask_base: usize, start_address: usize, size: usize) -> Self {
        Self { hart_mask, hart_mask_base, start_address, size }
    }
}

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVmaAsid {
    pub hart_mask: usize,
    pub hart_mask_base: usize,
    pub start_address: usize,
    pub size: usize,
    pub asid: usize,
}

impl SbiRemoteSfenceVmaAsid {
    pub fn new(hart_mask: usize, hart_mask_base: usize, start_address: usize, size: usize, asid: usize) -> Self {
        Self { hart_mask, hart_mask_base, start_address, size, asid }
    }
}
