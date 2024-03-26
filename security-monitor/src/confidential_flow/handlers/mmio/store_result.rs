// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioStorePending;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::ExposeToConfidentialVm;

#[derive(PartialEq)]
pub struct MmioStoreResult {
    instruction_length: usize,
}

impl MmioStoreResult {
    pub fn from_pending(request: MmioStorePending) -> Self {
        Self { instruction_length: request.instruction_length() }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        // let declassifier = DeclassifyToConfidentialVm::MmioStoreResult(result);
        self.declassify_to_confidential_hart(confidential_flow.confidential_hart_mut());
        confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::Nothing())
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.instruction_length;
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}
