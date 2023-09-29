// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::hart::{GpRegister, HartState};

#[derive(Debug)]
pub enum TrapReason {
    Interrupt,
    VsEcall(usize, usize),
    HsEcall(usize, usize),
    GuestLoadPageFault,
    GuestStorePageFault,
    StoreAccessFault,
    Unknown(usize, usize),
}

impl TrapReason {
    const STORE_ACCESS_FAULT: usize = 7;
    const HS_ECALL: usize = 9;
    const VS_ECALL: usize = 10;
    const GUEST_LOAD_PAGE_FAULT: usize = 21;
    const GUEST_STORE_PAGE_FAULT: usize = 23;

    pub fn from_hart_state(hart_state: &HartState) -> TrapReason {
        let mcause = riscv::register::mcause::read();
        if mcause.is_interrupt() {
            return TrapReason::Interrupt;
        }
        match mcause.code() {
            Self::STORE_ACCESS_FAULT => TrapReason::StoreAccessFault,
            Self::HS_ECALL => TrapReason::HsEcall(
                hart_state.gpr(GpRegister::a7),
                hart_state.gpr(GpRegister::a6),
            ),
            Self::VS_ECALL => TrapReason::VsEcall(
                hart_state.gpr(GpRegister::a7),
                hart_state.gpr(GpRegister::a6),
            ),
            Self::GUEST_LOAD_PAGE_FAULT => TrapReason::GuestLoadPageFault,
            Self::GUEST_STORE_PAGE_FAULT => TrapReason::GuestStorePageFault,
            _ => TrapReason::Unknown(
                hart_state.gpr(GpRegister::a7),
                hart_state.gpr(GpRegister::a6),
            ),
        }
    }
}
