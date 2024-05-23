// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::SbiIpi;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::{ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialHartRemoteCommandExecutable};

/// Handles a request from one confidential hart to execute sfence.vma instruction on remote confidential harts.
#[derive(Clone)]
pub struct SbiRemoteSfenceVma {
    ipi: SbiIpi,
    _start_address: usize,
    _size: usize,
}

impl SbiRemoteSfenceVma {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let ipi = SbiIpi::from_confidential_hart(confidential_hart);
        let _start_address = confidential_hart.gprs().read(GeneralPurposeRegister::a2);
        let _size = confidential_hart.gprs().read(GeneralPurposeRegister::a3);
        Self { ipi, _start_address, _size }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let transformation = confidential_flow
            .broadcast_confidential_hart_remote_command(ConfidentialHartRemoteCommand::SbiRemoteSfenceVma(self))
            .and_then(|_| Ok(SbiResponse::success(0)))
            .unwrap_or_else(|error| SbiResponse::error(error));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}

impl ConfidentialHartRemoteCommandExecutable for SbiRemoteSfenceVma {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        // TODO: execute a more fine grained fence. Right now, we just clear all tlbs
        crate::core::architecture::hfence_vvma();
        self.ipi.execute_on_confidential_hart(confidential_hart);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
