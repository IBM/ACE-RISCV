// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub enum CoviExtension {
    Unknown(usize, usize),
    InjectExternalInterrupt,
}

impl CoviExtension {
    pub const EXTID: usize = 0x434F5649;
    pub const SBI_EXT_COVI_TVM_AIA_INIT: usize = 0;
    pub const SBI_EXT_COVI_TVM_CPU_SET_IMSIC_ADDR: usize = 1;
    pub const SBI_EXT_COVI_TVM_CONVERT_IMSIC: usize = 2;
    pub const SBI_EXT_COVI_TVM_RECLAIM_IMSIC: usize = 3;
    pub const SBI_EXT_COVI_TVM_CPU_BIND_IMSIC: usize = 4;
    pub const SBI_EXT_COVI_TVM_CPU_UNBIND_IMSIC_BEGIN: usize = 5;
    pub const SBI_EXT_COVI_TVM_CPU_UNBIND_IMSIC_END: usize = 6;
    pub const SBI_EXT_COVI_TVM_CPU_INJECT_EXT_INTERRUPT: usize = 7;
    pub const SBI_EXT_COVI_TVM_REBIND_IMSIC_BEGIN: usize = 8;
    pub const SBI_EXT_COVI_TVM_REBIND_IMSIC_CLONE: usize = 9;
    pub const SBI_EXT_COVI_TVM_REBIND_IMSIC_END: usize = 10;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SBI_EXT_COVI_TVM_CPU_INJECT_EXT_INTERRUPT => Self::InjectExternalInterrupt,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
