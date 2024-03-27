// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResult;
use crate::confidential_flow::handlers::smp::SbiIpi;
use crate::confidential_flow::{ApplyToConfidentialVm, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, InterHartRequest};

#[derive(PartialEq, Debug, Clone)]
pub struct SbiRemoteSfenceVmaAsid {
    ipi: SbiIpi,
    start_address: usize,
    size: usize,
    asid: usize,
}

impl SbiRemoteSfenceVmaAsid {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        let asid = confidential_hart.gprs().read(GeneralPurposeRegister::a4);
        Self { ipi, start_address, size, asid }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_inter_hart_request(InterHartRequest::SbiRemoteSfenceVmaAsid(self))
            .and_then(|_| Ok(ApplyToConfidentialVm::SbiResult(SbiResult::success(0))))
            .unwrap_or_else(|error| error.into_confidential_transformation());
        confidential_flow.exit_to_confidential_hart(transformation)
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
