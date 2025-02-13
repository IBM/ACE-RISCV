// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use thiserror_no_std::Error;

#[derive(Error, Debug)]
pub enum TapError {
    #[error("Unsupported TAP Lockbox algorithm {0}")]
    UnsupportedLockboxAlgorithm(u16),
    #[error("Unsupported TAP digest entry type {0}")]
    UnsupportedDigestEntryType(u16),
    #[error("Unsupported TAP digest algorithm {0}")]
    UnsupportedDigestAlgorithm(u16),
    #[error("Unsupported TAP payload encryption algorithm {0}")]
    UnsupportedPayloadEncryptionAlgorithm(u16),
    #[error("Invalid magic in the beginning of TAP")]
    InvalidMagicStart(),
    #[error("Invalid size of the TAP")]
    InvalidSize(),
    #[error("Aes error {0}")]
    AesError(#[from] aes_gcm::Error),
    #[error("Key from slice error")]
    KeyCreationError(#[from] core::array::TryFromSliceError),
    #[error("KEM error")]
    KemError(),
    #[error("Could not find valid lockbox for this system")]
    NoLockboxFound(),
    #[error("Invalid size of TSK")]
    InvalidTskSize(),
}
