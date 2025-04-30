// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiRequest;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ResumableOperation;
use crate::non_confidential_flow::DeclassifyToHypervisor;

#[derive(Debug)]
pub enum TimeExtension {
    SetTimer,
    Unknown(usize, usize),
}

impl TimeExtension {
    pub const EXTID: usize = 0x54494D45;
    pub const SET_TIMER_FID: usize = 0x0;

    pub fn from_function_id(function_id: usize) -> Self {
        match function_id {
            Self::SET_TIMER_FID => Self::SetTimer,
            _ => Self::Unknown(Self::EXTID, function_id),
        }
    }
}
