// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::GeneralPurposeRegister;

/// Information stored in the confidential hart that requested MMIO load and is waiting for the response.
pub struct MmioLoadPending {
    instruction_length: usize,
    gpr_storing_load_result: GeneralPurposeRegister,
}

impl MmioLoadPending {
    pub fn new(instruction_length: usize, gpr_storing_load_result: GeneralPurposeRegister) -> Self {
        Self { instruction_length, gpr_storing_load_result }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }

    pub fn gpr_storing_load_result(&self) -> GeneralPurposeRegister {
        self.gpr_storing_load_result
    }
}
