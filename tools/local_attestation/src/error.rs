// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

// use thiserror_no_std::Error;
// #[derive(Error, Debug)]

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
    #[error("Tap Error")]
    TapSerializerError(tap::TapError),
    #[error("Int casting Error")]
    TryFromIntErr(#[from] std::num::TryFromIntError),
    #[error("Cannot open file {0}")]
    CannotOpenFile(String),
}

impl From<tap::TapError> for Error {
    fn from(err: tap::TapError) -> Self {
        Error::TapSerializerError(err)
    }
}

#[macro_export]
macro_rules! ensure {
    ($cond:expr, $error:expr) => {
        if !$cond {
            Err($error)
        } else {
            Ok(())
        }
    };
}
