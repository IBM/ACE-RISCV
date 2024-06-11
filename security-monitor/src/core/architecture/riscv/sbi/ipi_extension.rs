// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum IpiExtension {
    SendIpi,
    Unknown(usize, usize),
}

impl IpiExtension {
    pub const EXTID: usize = 0x735049;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::SendIpi,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
