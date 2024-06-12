// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum HsmExtension {
    HartStart,
    HartStop,
    HartGetStatus,
    HartSuspend,
    Unknown(usize, usize),
}

impl HsmExtension {
    pub const EXTID: usize = 0x48534D;
    pub const HART_START_FID: usize = 0x0;
    pub const HART_STOP_FID: usize = 0x1;
    pub const HART_STATUS_FID: usize = 0x2;
    pub const HART_SUSPEND_FID: usize = 0x3;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::HART_START_FID => Self::HartStart,
            Self::HART_STOP_FID => Self::HartStop,
            Self::HART_STATUS_FID => Self::HartGetStatus,
            Self::HART_SUSPEND_FID => Self::HartSuspend,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
