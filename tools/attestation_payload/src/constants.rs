// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub const ACE_TAP_MAGIC: u32 = 0xACEACE00;

#[repr(u8)]
pub enum TapDigestEntryType {
    Kernel,
    KernelCommandLine,
    Initramfs
}

#[repr(u8)]
pub enum TapDigestAlgorithm {
    Sha512,
}

impl TapDigestAlgorithm {
    pub fn digest_size(&self) -> u16 {
        match self {
            &Self::Sha512 => 512/8,
        }
    }
}

#[repr(u8)]
pub enum TapLockboxAlgorithm {
    Rsa_2048_Sha256_OASP = 0,
}