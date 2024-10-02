// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use alloc::vec::Vec;

pub const ACE_HEADER_SIZE: usize = 4;
pub const ACE_FOOTER_SIZE: usize = 4;
pub const ACE_MAGIC_TAP_START: u16 = 0xACE0;
pub const ACE_MAGIC_TAP_END: u16 = 0xACE1;

pub struct TeeAttestationPayload {
    pub lockboxes: Vec<Lockbox>,
    pub digests: Vec<TapDigest>,
    pub secrets: Vec<TapSecret>,
}

pub struct Lockbox {
    pub name: u64,
    pub algorithm: TapLockboxAlgorithm,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
pub enum TapLockboxAlgorithm {
    Debug = 0,
    Rsa2048Sha256Oasp = 1,
}

impl TapLockboxAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::Rsa2048Sha256Oasp),
            v => Err(TapError::UnsupportedTapLockboxAlgorithm(v)),
        }
    }
}

pub struct TapDigest {
    pub entry_type: TapDigestEntryType,
    pub algorithm: TapDigestAlgorithm,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
pub enum TapDigestEntryType {
    Kernel = 0,
    KernelCommandLine = 1,
    Initramfs = 2,
}

impl TapDigestEntryType {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Kernel),
            1 => Ok(Self::KernelCommandLine),
            2 => Ok(Self::Initramfs),
            v => Err(TapError::UnsupportedTapDigestEntryType(v)),
        }
    }
}

#[repr(u16)]
#[derive(Debug)]
pub enum TapDigestAlgorithm {
    Debug = 0,
    Sha512 = 1,
}

impl TapDigestAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::Sha512),
            v => Err(TapError::UnsupportedTapDigestAlgorithm(v)),
        }
    }

    pub fn digest_size(&self) -> u16 {
        match self {
            &Self::Debug => 0,
            &Self::Sha512 => 512 / 8,
        }
    }
}

pub struct TapSecret {
    pub name: u64,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
pub enum TapPayloadEncryptionAlgorithm {
    Debug = 0,
    AesGcm256 = 1,
}

impl TapPayloadEncryptionAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::AesGcm256),
            v => Err(TapError::UnsupportedTapPayloadEncryptionAlgorithm(v)),
        }
    }
}