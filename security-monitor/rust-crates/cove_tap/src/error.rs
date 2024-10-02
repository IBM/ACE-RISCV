// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use thiserror_no_std::Error;

#[derive(Error, Debug)]
pub enum TapError {
    #[error("Unsupported TAP Lockbox algorithm {0}")]
    UnsupportedTapLockboxAlgorithm(u16),
    #[error("Unsupported TAP digest entry type {0}")]
    UnsupportedTapDigestEntryType(u16),
    #[error("Unsupported TAP digest algorithm {0}")]
    UnsupportedTapDigestAlgorithm(u16),
    #[error("Unsupported TAP payload encryption algorithm {0}")]
    UnsupportedTapPayloadEncryptionAlgorithm(u16),
    #[error("Invalid magic in the beginning of TAP")]
    InvalidMagicStart(),
    #[error("Invalid size of the TAP")]
    InvalidSize(),

    #[error("Aes error {0}")]
    AesError(#[from] aes_gcm::Error)

}