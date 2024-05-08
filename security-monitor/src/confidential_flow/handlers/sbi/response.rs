// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToConfidentialVm};
use crate::core::architecture::{GeneralPurposeRegister, ECALL_INSTRUCTION_LENGTH};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::error::Error;

/// Handles a response to the hypercall. This response comes from the hypervisor and carries a result of a hypercall
/// requested by the confidential hart.
pub struct SbiResponse {
    a0: usize,
    a1: usize,
}

impl SbiResponse {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self { a0: hypervisor_hart.gprs().read(GeneralPurposeRegister::a0), a1: hypervisor_hart.gprs().read(GeneralPurposeRegister::a1) }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.declassify_and_exit_to_confidential_hart(DeclassifyToConfidentialVm::SbiResponse(self))
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        debug!("SBI result: {} {}", self.a0, self.a1);
        self.apply_to_confidential_hart(confidential_hart);
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        confidential_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        let new_mepc = confidential_hart.csrs().mepc.read_value() + ECALL_INSTRUCTION_LENGTH;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + ECALL_INSTRUCTION_LENGTH;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
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
