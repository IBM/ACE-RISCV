// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::SbiExtension;
use crate::core::architecture::HartArchitecturalState;

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
    GuestStorePageFault,
    Unknown(usize),
}

impl TrapReason {
    // Below constants are defined in the RISC-V privilege spec. See the table defining
    // the machine cause register (mcause) values after trap.
    const ILLEGAL_INSTRUCTION: usize = 2;
    const LOAD_ADDRESS_MISALIGNED: usize = 4;
    const LOAD_ACCESS_FAULT: usize = 5;
    const STORE_ADDRESS_MISALIGNED: usize = 6;
    const STORE_ACCESS_FAULT: usize = 7;
    const HYPERVISOR_ECALL: usize = 9;
    const VIRTUAL_SUPERVISOR_ECALL: usize = 10;
    const MACHINE_ECALL: usize = 11;
    const GUEST_INSTRUCTION_PAGE_FAULT: usize = 20;
    const GUEST_LOAD_PAGE_FAULT: usize = 21;
    const GUEST_STORE_PAGE_FAULT: usize = 23;

    pub fn from_hart_state(hart_state: &HartArchitecturalState) -> Self {
        let mcause = riscv::register::mcause::read();
        if mcause.is_interrupt() {
            Self::Interrupt
        } else {
            match mcause.code() {
                Self::ILLEGAL_INSTRUCTION => Self::IllegalInstruction,
                Self::LOAD_ADDRESS_MISALIGNED => Self::LoadAddressMisaligned,
                Self::LOAD_ACCESS_FAULT => Self::LoadAccessFault,
                Self::STORE_ADDRESS_MISALIGNED => Self::StoreAddressMisaligned,
                Self::STORE_ACCESS_FAULT => Self::StoreAccessFault,
                Self::HYPERVISOR_ECALL => Self::HsEcall(SbiExtension::decode(hart_state)),
                Self::VIRTUAL_SUPERVISOR_ECALL => Self::VsEcall(SbiExtension::decode(hart_state)),
                Self::MACHINE_ECALL => Self::MachineEcall,
                Self::GUEST_INSTRUCTION_PAGE_FAULT => Self::GuestInstructionPageFault,
                Self::GUEST_LOAD_PAGE_FAULT => Self::GuestLoadPageFault,
                Self::GUEST_STORE_PAGE_FAULT => Self::GuestStorePageFault,
                mcause => Self::Unknown(mcause),
            }
        }
    }
}
