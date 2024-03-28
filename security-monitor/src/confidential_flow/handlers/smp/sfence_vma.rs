// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::smp::SbiIpi;
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, InterHartRequest};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVma {
    ipi: SbiIpi,
    start_address: usize,
    size: usize,
}

impl SbiRemoteSfenceVma {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        Self { ipi, start_address, size }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiRemoteSfenceVma(self))
            .and_then(|_| Ok(ApplyToConfidentialVm::SbiResponse(SbiResponse::success(0))))
            .unwrap_or_else(|error| error.into_confidential_transformation());
        confidential_flow.apply_and_exit_to_confidential_hart(transformation)
    }

    pub fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_vvma();
        self.ipi.execute_on_confidential_hart(confidential_hart);
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
