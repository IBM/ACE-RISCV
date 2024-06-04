// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::{F_EXTENSION, V_EXTENSION};

pub mod compressed_instructions;
pub mod floating_point;
pub mod vector_registers;

#[derive(PartialEq, Debug)]
pub enum IsaOptionalExtension {
    FloatingPointExtension,
    VectorExtension,
}

impl IsaOptionalExtension {
    pub fn code(&self) -> &str {
        match self {
            Self::FloatingPointExtension => F_EXTENSION,
            Self::VectorExtension => V_EXTENSION,
        }
    }

    pub fn all() -> [IsaOptionalExtension; 2] {
        [Self::FloatingPointExtension, Self::VectorExtension]
    }
}
