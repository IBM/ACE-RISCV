// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState};
use crate::core::control_data::{ConfidentialHart, HardwareHart};
use crate::core::transformations::mmio_pending::{MmioLoadPending, MmioStorePending};

pub struct MmioLoadResult {
    value: usize,
    result_gpr: GeneralPurposeRegister,
    instruction_length: usize,
}

impl MmioLoadResult {
    pub fn from_hardware_hart(hardware_hart: &HardwareHart, request: MmioLoadPending) -> Self {
        Self {
            result_gpr: request.result_gpr(),
            value: hardware_hart.gprs().read(request.result_gpr()),
            instruction_length: request.instruction_length(),
        }
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.confidential_hart_state_mut().gprs_mut().write(self.result_gpr, self.value);
        let new_mepc = confidential_hart.confidential_hart_state().csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.confidential_hart_state_mut().csrs_mut().mepc.save_value(new_mepc);
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

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.confidential_hart_state().csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.confidential_hart_state_mut().csrs_mut().mepc.save_value(new_mepc);
    }
}
