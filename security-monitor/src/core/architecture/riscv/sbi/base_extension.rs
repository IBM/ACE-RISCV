// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum BaseExtension {
    GetSpecVersion,
    GetImplId,
    GetImplVersion,
    ProbeExtension,
    GetMvendorId,
    GetMarchid,
    GetMimpid,
    Unknown(usize, usize),
}

impl BaseExtension {
    pub const EXTID: usize = 0x10;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::GetSpecVersion,
            1 => Self::GetImplId,
            2 => Self::GetImplVersion,
            3 => Self::ProbeExtension,
            4 => Self::GetMvendorId,
            5 => Self::GetMarchid,
            6 => Self::GetMimpid,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
