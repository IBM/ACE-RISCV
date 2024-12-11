// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::symmetrical_multiprocessing::Ipi;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialHartRemoteCommand, ConfidentialHartRemoteCommandExecutable, ControlDataStorage,
};

/// Handles a request from one confidential hart to execute fence.i instruction on remote confidential harts.
#[derive(Clone)]
pub struct RemoteFenceI {
    ipi: Ipi,
}

impl RemoteFenceI {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { ipi: Ipi::from_confidential_hart(confidential_hart) }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        let result = ControlDataStorage::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |mut confidential_vm| {
            confidential_flow.broadcast_remote_command(&mut confidential_vm, ConfidentialHartRemoteCommand::RemoteFenceI(self))
        })
        .map_or_else(|error| SbiResponse::error(error), |_| SbiResponse::success());
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(result))
    }
}

impl ConfidentialHartRemoteCommandExecutable for RemoteFenceI {
    fn execute_on_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        crate::core::architecture::riscv::fence::fence_i();
        self.ipi.execute_on_confidential_hart(confidential_hart);
    }

    fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.ipi.is_hart_selected(hart_id)
    }
}
