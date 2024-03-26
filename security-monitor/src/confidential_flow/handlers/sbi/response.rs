// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{GeneralPurposeRegister, ECALL_INSTRUCTION_LENGTH};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::transformations::ExposeToConfidentialVm;

/// Sbi is a result of the SBI call from the Hypervisor to the SBI
/// firmware or a result of the SBI call to the security monitor.
#[derive(Debug)]
pub struct SbiResult {
    a0: usize,
    a1: usize,
    pc_offset: usize,
}

impl SbiResult {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        Self::new(
            hypervisor_hart.gprs().read(GeneralPurposeRegister::a0),
            hypervisor_hart.gprs().read(GeneralPurposeRegister::a1),
            ECALL_INSTRUCTION_LENGTH,
        )
    }

    /// Handles a response to the hypercall. This response comes from the hypervisor and carries a result of a hypercall
    /// requested by the confidential hart.
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        // let declassifier = DeclassifyToConfidentialVm::SbiResult(result);
        self.declassify_to_confidential_hart(confidential_flow.confidential_hart_mut());
        confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::Nothing())
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        confidential_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.pc_offset;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }

    pub fn declassify_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + self.pc_offset;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart) {
        let new_mepc = hypervisor_hart.csrs().mepc.read_value() + self.pc_offset;
        hypervisor_hart.csrs_mut().mepc.save_value(new_mepc);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a0, self.a0);
        hypervisor_hart.gprs_mut().write(GeneralPurposeRegister::a1, self.a1);
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
}
