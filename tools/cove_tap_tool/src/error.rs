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
    #[error("Tap Error")]
    TapSerializerError(riscv_cove_tap::TapError),
    #[error("Int casting Error")]
    TryFromIntErr(#[from] std::num::TryFromIntError),
    #[error("Cannot open file {0}")]
    CannotOpenFile(String),
    #[error("Could not parse int")]
    IntParseError(#[from] core::num::ParseIntError),
    #[error("Placeholder error")]
    PlaceholderError(),
}

impl From<riscv_cove_tap::TapError> for Error {
    fn from(err: riscv_cove_tap::TapError) -> Self {
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
