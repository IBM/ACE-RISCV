// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::MmioLoadPending;
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToConfidentialVm};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};

pub struct MmioLoadResponse {
    value: usize,
    request: MmioLoadPending,
}

impl MmioLoadResponse {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart, request: MmioLoadPending) -> Self {
        let value = hypervisor_hart.shared_memory().gpr(request.gpr_storing_load_result());
        Self { value, request }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        confidential_flow.declassify_and_exit_to_confidential_hart(DeclassifyToConfidentialVm::MmioLoadResponse(self))
    }

    pub fn declassify_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        debug!("MMIO LOAD read: {:x}", self.value);
        confidential_hart.gprs_mut().write(self.request.gpr_storing_load_result(), self.value);
        let new_mepc = confidential_hart.csrs().mepc.read_value() + self.request.instruction_length();
        confidential_hart.csrs_mut().mepc.save_value(new_mepc);
    }
}
