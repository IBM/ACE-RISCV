// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum SrstExtension {
    SystemReset,
    Unknown(usize, usize),
}

impl SrstExtension {
    pub const EXTID: usize = 0x53525354;
    pub const SYSTEM_RESET_FID: usize = 0x0;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SYSTEM_RESET_FID => Self::SystemReset,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
