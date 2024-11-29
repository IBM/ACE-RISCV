// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub struct ConfidentialVmMemoryLayout {
    kernel: (usize, usize),
    fdt: (usize, usize),
    initrd: Option<(usize, usize)>,
}

impl ConfidentialVmMemoryLayout {
    pub fn new(kernel: (usize, usize), fdt: (usize, usize), initrd: Option<(usize, usize)>) -> Self {
        Self { kernel, fdt, initrd }
    }

    pub fn is_kernel(&self, address: usize) -> bool {
        self.kernel.0 <= address && address < self.kernel.1
    }

    pub fn is_fdt(&self, address: usize) -> bool {
        self.fdt.0 <= address && address < self.fdt.1
    }

    pub fn is_initrd(&self, address: usize) -> bool {
        self.initrd.and_then(|o| Some(o.0 <= address && address < o.1)).unwrap_or(false)
    }
}
