// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Debug, Clone)]
pub struct SbiIpi {
    hart_mask: usize,
    hart_mask_base: usize,
}

impl SbiIpi {
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
