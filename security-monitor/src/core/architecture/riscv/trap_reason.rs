// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use super::specification::*;
use crate::core::architecture::riscv::sbi::SbiExtension;

#[derive(Debug)]
pub enum TrapReason {
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

impl TrapReason {
    pub fn from(mcause: usize, a7: usize, a6: usize) -> Self {
        if (mcause & 1usize << CAUSE_INTERRUPT_BIT) > 0 {
            Self::Interrupt
        } else {
            match mcause as u8 {
                CAUSE_ILLEGAL_INSTRUCTION => Self::IllegalInstruction,
                CAUSE_MISALIGNED_LOAD => Self::LoadAddressMisaligned,
                CAUSE_LOAD_ACCESS => Self::LoadAccessFault,
                CAUSE_MISALIGNED_STORE => Self::StoreAddressMisaligned,
                CAUSE_STORE_ACCESS => Self::StoreAccessFault,
                CAUSE_SUPERVISOR_ECALL => Self::HsEcall(SbiExtension::decode(a7, a6)),
                CAUSE_VIRTUAL_SUPERVISOR_ECALL => Self::VsEcall(SbiExtension::decode(a7, a6)),
                CAUSE_MACHINE_ECALL => Self::MachineEcall,
                CAUSE_FETCH_GUEST_PAGE_FAULT => Self::GuestInstructionPageFault,
                CAUSE_LOAD_GUEST_PAGE_FAULT => Self::GuestLoadPageFault,
                CAUSE_VIRTUAL_INSTRUCTION => Self::VirtualInstruction,
                CAUSE_STORE_GUEST_PAGE_FAULT => Self::GuestStorePageFault,
                mcause => Self::Unknown(mcause),
            }
        }
    }
}
