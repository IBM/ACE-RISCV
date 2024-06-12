// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum CovgExtension {
    AddMmioRegion,
    RemoveMmioRegion,
    ShareMemory,
    UnshareMemory,
    AllowExternalInterrupt,
    DenyExternalInterrupt,
    Unknown(usize, usize),
}

impl CovgExtension {
    pub const EXTID: usize = 0x434F5647;
    pub const SBI_EXT_COVG_ADD_MMIO_REGION: usize = 0;
    pub const SBI_EXT_COVG_REMOVE_MMIO_REGION: usize = 1;
    pub const SBI_EXT_COVG_SHARE_MEMORY: usize = 2;
    pub const SBI_EXT_COVG_UNSHARE_MEMORY: usize = 3;
    pub const SBI_EXT_COVG_ALLOW_EXT_INTERRUPT: usize = 4;
    pub const SBI_EXT_COVG_DENY_EXT_INTERRUPT: usize = 5;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SBI_EXT_COVG_ADD_MMIO_REGION => Self::AddMmioRegion,
            Self::SBI_EXT_COVG_REMOVE_MMIO_REGION => Self::RemoveMmioRegion,
            Self::SBI_EXT_COVG_SHARE_MEMORY => Self::ShareMemory,
            Self::SBI_EXT_COVG_UNSHARE_MEMORY => Self::UnshareMemory,
            Self::SBI_EXT_COVG_ALLOW_EXT_INTERRUPT => Self::AllowExternalInterrupt,
            Self::SBI_EXT_COVG_DENY_EXT_INTERRUPT => Self::DenyExternalInterrupt,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
