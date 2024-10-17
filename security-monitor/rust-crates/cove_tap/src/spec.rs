// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use alloc::vec::Vec;

pub const ACE_HEADER_SIZE: usize = 8;
pub const ACE_FOOTER_SIZE: usize = 8;
pub const ACE_MAGIC_TAP_START: u32 = 0xACE0ACE0;
pub const ACE_MAGIC_TAP_END: u32 = 0xACE1ACE1;
pub const ACE_MAX_TAP_SIZE: usize = 4096; // size of the 4KiB page

pub struct AttestationPayload {
    pub lockboxes: Vec<Lockbox>,
    pub digests: Vec<Digest>,
    pub secrets: Vec<Secret>,
}

pub struct Lockbox {
    pub name: u64,
    pub algorithm: LockboxAlgorithm,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
pub enum LockboxAlgorithm {
    Debug = 0,
    Rsa2048Sha256Oasp = 1,
}

impl LockboxAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::Rsa2048Sha256Oasp),
            v => Err(TapError::UnsupportedLockboxAlgorithm(v)),
        }
    }
}

pub struct Digest {
    pub pcr_id: u16,
    pub algorithm: DigestAlgorithm,
    pub value: Vec<u8>,
}

impl Digest {
    pub fn value_in_hex(&self) -> alloc::string::String {
        use crate::alloc::string::ToString;
        self.value.iter().map(|b| alloc::format!("{:02x}", b).to_string()).collect::<Vec<alloc::string::String>>().join("")
    }

    pub fn pcr_id(&self) -> u16 {
        self.pcr_id
    }
}

#[repr(u16)]
#[derive(Debug, PartialEq, Eq)]
pub enum DigestAlgorithm {
    Debug = 0,
    Sha512 = 1,
}

impl DigestAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::Sha512),
            v => Err(TapError::UnsupportedDigestAlgorithm(v)),
        }
    }

    pub fn digest_size(&self) -> u16 {
        match self {
            &Self::Debug => 0,
            &Self::Sha512 => 512 / 8,
        }
    }
}

pub struct Secret {
    pub name: u64,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
pub enum PayloadEncryptionAlgorithm {
    Debug = 0,
    AesGcm256 = 1,
}

impl PayloadEncryptionAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::AesGcm256),
            v => Err(TapError::UnsupportedPayloadEncryptionAlgorithm(v)),
        }
    }
}