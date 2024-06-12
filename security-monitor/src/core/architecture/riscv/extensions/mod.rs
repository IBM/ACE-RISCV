// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::{F_EXTENSION, SSTC_EXTENSION, V_EXTENSION};

pub mod compressed_instructions;
pub mod floating_point_unit;
pub mod supervisor_timer_extension;
pub mod vector_unit;

#[derive(PartialEq, Debug)]
pub enum HardwareExtension {
    FloatingPointExtension,
    VectorExtension,
    SupervisorTimerExtension,
}

impl HardwareExtension {
    pub fn code(&self) -> &str {
        match self {
            Self::FloatingPointExtension => F_EXTENSION,
            Self::VectorExtension => V_EXTENSION,
            Self::SupervisorTimerExtension => SSTC_EXTENSION,
        }
    }

    pub fn all() -> [HardwareExtension; 3] {
        [Self::FloatingPointExtension, Self::VectorExtension, Self::SupervisorTimerExtension]
    }
}
