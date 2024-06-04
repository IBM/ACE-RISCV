// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioStorePending;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToConfidentialVm};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

/// Handles MMIO store response coming from the hypervisor.
pub struct MmioStoreResponse {
    instruction_length: usize,
}

impl MmioStoreResponse {
    pub fn from_hypervisor_hart(_: &HypervisorHart, request: MmioStorePending) -> Self {
        Self { instruction_length: request.instruction_length() }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.declassify_and_exit_to_confidential_hart(DeclassifyToConfidentialVm::MmioStoreResponse(self))
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        confidential_hart.csrs_mut().mepc.add(self.instruction_length);
    }
}
