// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("IO Error")]
    IoError(#[from] std::io::Error),
    #[error("PKCS1 Error")]
    Pkcs1Error(#[from] rsa::pkcs1::Error),
    #[error("RSA Error")]
    RsaError(#[from] rsa::Error),
    #[error("Invalid parameter")]
    InvalidParameter(String),

    #[error("Int casting Error")]
    TryFromIntErr(#[from] std::num::TryFromIntError),

    #[error("Symmetric key size does not match the HMAC function")]
    InvalidSizeOfSymmetricKey(),

    #[error("Cannot open file {0}")]
    CannotOpenFile(String),
}
