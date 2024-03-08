// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::specification::*;
use super::supervisor_binary_interface::SbiExtension;
use crate::core::architecture::is_bit_enabled;

#[derive(Debug)]
pub enum TrapCause {
    Interrupt,
    IllegalInstruction,
    LoadAddressMisaligned,
    LoadAccessFault,
    StoreAddressMisaligned,
    StoreAccessFault,
    VsEcall(SbiExtension),
    HsEcall(SbiExtension),
    MachineEcall,
    GuestInstructionPageFault,
    GuestLoadPageFault,
    VirtualInstruction,
    GuestStorePageFault,
    Unknown(u8),
}

impl TrapCause {
    pub fn from(cause: usize, extension_id: usize, function_id: usize) -> Self {
        if is_bit_enabled(cause, CAUSE_INTERRUPT_BIT) {
            Self::Interrupt
        } else {
            match cause as u8 {
                CAUSE_ILLEGAL_INSTRUCTION => Self::IllegalInstruction,
                CAUSE_MISALIGNED_LOAD => Self::LoadAddressMisaligned,
                CAUSE_LOAD_ACCESS => Self::LoadAccessFault,
                CAUSE_MISALIGNED_STORE => Self::StoreAddressMisaligned,
                CAUSE_STORE_ACCESS => Self::StoreAccessFault,
                CAUSE_SUPERVISOR_ECALL => Self::HsEcall(SbiExtension::decode(extension_id, function_id)),
                CAUSE_VIRTUAL_SUPERVISOR_ECALL => Self::VsEcall(SbiExtension::decode(extension_id, function_id)),
                CAUSE_MACHINE_ECALL => Self::MachineEcall,
                CAUSE_FETCH_GUEST_PAGE_FAULT => Self::GuestInstructionPageFault,
                CAUSE_LOAD_GUEST_PAGE_FAULT => Self::GuestLoadPageFault,
                CAUSE_VIRTUAL_INSTRUCTION => Self::VirtualInstruction,
                CAUSE_STORE_GUEST_PAGE_FAULT => Self::GuestStorePageFault,
                cause => Self::Unknown(cause),
            }
        }
    }
}
