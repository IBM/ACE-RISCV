// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GpRegister, HartState};
use crate::core::transformations::GuestLoadPageFaultRequest;

pub struct GuestLoadPageFaultResult {
    value: usize,
    result_gpr: GpRegister,
    instruction_length: usize,
}

impl GuestLoadPageFaultResult {
    pub fn new(hart_state: &HartState, request: GuestLoadPageFaultRequest) -> Self {
        Self {
            result_gpr: request.result_gpr(),
            value: hart_state.gpr(request.result_gpr()),
            instruction_length: request.instruction_length(),
        }
    }

    pub fn value(&self) -> usize {
        self.value
    }

    pub fn result_gpr(&self) -> GpRegister {
        self.result_gpr
    }

    pub fn instruction_length(&self) -> usize {
        self.instruction_length
    }
}
