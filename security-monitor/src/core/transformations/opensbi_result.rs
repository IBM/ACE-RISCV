// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Debug)]
pub struct OpensbiResult {
    pub trap_regs: opensbi_sys::sbi_trap_regs,
}

impl OpensbiResult {
    pub fn from_opensbi_handler(trap_regs: opensbi_sys::sbi_trap_regs) -> Self {
        Self { trap_regs }
    }
}
