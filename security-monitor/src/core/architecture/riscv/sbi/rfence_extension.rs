// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum RfenceExtension {
    RemoteFenceI,
    RemoteSfenceVma,
    RemoteSfenceVmaAsid,
    RemoteHfenceGvmaVmid,
    RemoteHfenceGvma,
    RemoteHfenceVvmaAsid,
    RemoteHfenceVvma,
    Unknown(usize, usize),
}

impl RfenceExtension {
    pub const EXTID: usize = 0x52464E43;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            0 => Self::RemoteFenceI,
            1 => Self::RemoteSfenceVma,
            2 => Self::RemoteSfenceVmaAsid,
            3 => Self::RemoteHfenceGvmaVmid,
            4 => Self::RemoteHfenceGvma,
            5 => Self::RemoteHfenceVvmaAsid,
            6 => Self::RemoteHfenceVvma,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
