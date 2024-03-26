// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioLoadPending;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::transformations::ExposeToConfidentialVm;

pub struct MmioLoadResult {
    value: usize,
    result_gpr: GeneralPurposeRegister,
    instruction_length: usize,
}

impl MmioLoadResult {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart, request: MmioLoadPending) -> Self {
        Self {
            result_gpr: request.result_gpr(),
            value: hypervisor_hart.gprs().read(request.result_gpr()),
            instruction_length: request.instruction_length(),
        }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        // let declassifier = DeclassifyToConfidentialVm::MmioLoadResult(result);
        self.declassify_to_confidential_hart(confidential_flow.confidential_hart_mut());
        confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::Nothing())
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.gprs_mut().write(self.result_gpr, self.value);
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}
