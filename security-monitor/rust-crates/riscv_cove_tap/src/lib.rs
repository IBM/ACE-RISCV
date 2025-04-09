// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]
extern crate alloc;

mod error;
#[cfg(feature = "parser")]
mod parser;
#[cfg(feature = "serializer")]
mod serializer;

#[cfg(feature = "parser")]
pub use parser::AttestationPayloadParser;

#[cfg(feature = "serializer")]
pub use serializer::AttestationPayloadSerializer;

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

pub use spec::*;
pub use error::*;
pub mod spec;
