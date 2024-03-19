// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub struct OpensbiResult {
    trap_regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiResult {
    pub fn from_opensbi_handler(trap_regs: opensbi_sys::sbi_trap_regs) -> Self {
        Self { trap_regs }
    }

    pub fn mstatus(&self) -> usize {
        self.trap_regs.mstatus.try_into().unwrap()
    }

    pub fn mepc(&self) -> usize {
        self.trap_regs.mepc.try_into().unwrap()
    }

    pub fn a0(&self) -> usize {
        self.trap_regs.a0.try_into().unwrap()
    }

    pub fn a1(&self) -> usize {
        self.trap_regs.a1.try_into().unwrap()
    }
}
