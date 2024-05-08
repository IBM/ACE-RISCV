// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, ECALL_INSTRUCTION_LENGTH};
use crate::core::control_data::HypervisorHart;
use crate::error::Error;

pub struct SbiResponse {
    a0: usize,
    a1: usize,
}

impl SbiResponse {
    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + ECALL_INSTRUCTION_LENGTH;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
    }

    pub fn success(code: usize) -> Self {
        Self { a0: 0, a1: code }
    }

    pub fn failure(code: usize) -> Self {
        Self { a0: code, a1: 0 }
    }

    pub fn error(error: Error) -> Self {
        Self::failure(error.code())
    }
}
