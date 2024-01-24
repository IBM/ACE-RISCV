// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::SbiExtension;
use crate::core::architecture::HartArchitecturalState;

#[derive(Debug)]
pub enum TrapReason {
    Interrupt,
    VsEcall(SbiExtension),
    HsEcall(SbiExtension),
    GuestLoadPageFault,
    GuestStorePageFault,
    StoreAccessFault,
    Unknown,
}

impl TrapReason {
    // Below constants are defined in the RISC-V privilege spec. See the table defining
    // the machine cause register (mcause) values after trap.
    const STORE_ACCESS_FAULT: usize = 7;
    const HS_ECALL: usize = 9;
    const VS_ECALL: usize = 10;
    const GUEST_LOAD_PAGE_FAULT: usize = 21;
    const GUEST_STORE_PAGE_FAULT: usize = 23;

    pub fn from_hart_state(hart_state: &HartArchitecturalState) -> Self {
        let mcause = riscv::register::mcause::read();
        if mcause.is_interrupt() {
            return Self::Interrupt;
        }
        match mcause.code() {
            Self::STORE_ACCESS_FAULT => Self::StoreAccessFault,
            Self::HS_ECALL => Self::HsEcall(SbiExtension::decode(hart_state)),
            Self::VS_ECALL => Self::VsEcall(SbiExtension::decode(hart_state)),
            Self::GUEST_LOAD_PAGE_FAULT => Self::GuestLoadPageFault,
            Self::GUEST_STORE_PAGE_FAULT => Self::GuestStorePageFault,
            _ => Self::Unknown,
        }
    }
}
