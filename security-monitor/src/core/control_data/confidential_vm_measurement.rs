// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

const MAX_HASH_SIZE: usize = 512; // 512b for SHA-512

#[derive(Clone, Copy)]
pub struct ConfidentialVmMeasurement {
    pub value: [u8; MAX_HASH_SIZE / 8],
}

impl ConfidentialVmMeasurement {
    pub const fn empty() -> Self {
        Self { value: [0u8; MAX_HASH_SIZE / 8] }
    }
}
