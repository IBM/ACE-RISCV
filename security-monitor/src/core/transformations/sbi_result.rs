// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState, ECALL_INSTRUCTION_LENGTH};

/// Sbi is a result of the SBI call from the Hypervisor to the SBI
/// firmware or a result of the SBI call to the security monitor.
#[derive(Debug)]
pub struct SbiResult {
    a0: usize,
    a1: usize,
    pc_offset: usize,
}

impl SbiResult {
    pub fn ecall(hart_state: &HartArchitecturalState) -> Self {
        Self::new(hart_state.gpr(GeneralPurposeRegister::a0), hart_state.gpr(GeneralPurposeRegister::a1), ECALL_INSTRUCTION_LENGTH)
    }

    pub fn success(code: usize) -> Self {
        Self::new(0, code, ECALL_INSTRUCTION_LENGTH)
    }

    pub fn failure(code: usize) -> Self {
        Self::new(code, 0, ECALL_INSTRUCTION_LENGTH)
    }

    fn new(a0: usize, a1: usize, pc_offset: usize) -> Self {
        Self { a0, a1, pc_offset }
    }

    pub fn a0(&self) -> usize {
        self.a0
    }

    pub fn a1(&self) -> usize {
        self.a1
    }

    pub fn pc_offset(&self) -> usize {
        self.pc_offset
    }
}
