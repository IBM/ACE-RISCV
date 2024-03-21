// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::transformations::mmio_pending::{MmioLoadPending, MmioStorePending};

pub struct MmioLoadResult {
    value: usize,
    result_gpr: GeneralPurposeRegister,
    instruction_length: usize,
}

impl MmioLoadResult {
    pub fn new(hart_state: &HartArchitecturalState, request: MmioLoadPending) -> Self {
        Self {
            result_gpr: request.result_gpr(),
            value: hart_state.gpr(request.result_gpr()),
            instruction_length: request.instruction_length(),
        }
    }

    pub fn value(&self) -> usize {
        self.value
    }

    pub fn result_gpr(&self) -> GeneralPurposeRegister {
        self.result_gpr
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}

#[derive(PartialEq)]
pub struct MmioStoreResult {
    instruction_length: usize,
}

impl MmioStoreResult {
    pub fn new(request: MmioStorePending) -> Self {
        Self { instruction_length: request.instruction_length() }
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
