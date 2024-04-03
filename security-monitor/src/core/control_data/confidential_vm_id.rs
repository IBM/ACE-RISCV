// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Copy, Clone, Debug)]
pub struct ConfidentialVmId(usize);

impl ConfidentialVmId {
    pub fn new(value: usize) -> Self {
        Self(value)
    }

    pub fn usize(&self) -> usize {
        self.0
    }
}
