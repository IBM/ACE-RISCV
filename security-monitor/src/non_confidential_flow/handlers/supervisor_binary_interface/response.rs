// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::SBI_SUCCESS;
use crate::core::architecture::riscv::specification::ECALL_INSTRUCTION_LENGTH;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::error::Error;

pub struct SbiResponse {
    pub a0: usize,
    pub a1: usize,
}

impl SbiResponse {
    pub fn success() -> Self {
        Self::success_with_code(0)
    }

    pub fn success_with_code(code: usize) -> Self {
        Self { a0: SBI_SUCCESS as usize, a1: code }
    }

    pub fn error(error: Error) -> Self {
        Self { a0: error.sbi_error_code(), a1: 0 }
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.csrs_mut().mepc.add(ECALL_INSTRUCTION_LENGTH);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
    }
}
