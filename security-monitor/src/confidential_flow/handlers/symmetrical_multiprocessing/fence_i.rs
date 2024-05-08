// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiIpi;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::{ConfidentialHart, InterHartRequest, InterHartRequestExecutable};

/// Handles a request from one confidential hart to execute fence.i instruction on remote confidential harts.
#[derive(Clone)]
pub struct SbiRemoteFenceI {
    ipi: SbiIpi,
}

impl SbiRemoteFenceI {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { ipi: SbiIpi::from_confidential_hart(confidential_hart) }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiRemoteFenceI(self))
            .and_then(|_| Ok(SbiResponse::success(0)))
            .unwrap_or_else(|error| SbiResponse::success(error.code()));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}

impl InterHartRequestExecutable for SbiRemoteFenceI {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        crate::core::architecture::fence_i();
        self.ipi.execute_on_confidential_hart(confidential_hart);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
