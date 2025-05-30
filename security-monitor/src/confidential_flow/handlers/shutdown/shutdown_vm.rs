// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::control_data::{ConfidentialHart, ConfidentialHartRemoteCommand, ControlDataStorage};

/// Handles the system reset call of the SBI's SRST extension. This call is a request to shutdown or reboot the
/// confidential virtual machine. The security monitor allows only for the full shutdown of the confidential virtual
/// machine and thus, it treats every call to this function as a VM shutdown.
///
/// To shutdown the entire confidential VM and remove it from the control data memory, all confidential harts must be
/// shutdown (lifecycle state `Shutdown`). To do so, we send `Shutdown IPI` to all confidential harts. The last
/// confidential hart that shutdowns itself, will remove the entire confidential VM from the control data.
#[derive(Clone, PartialEq)]
pub struct ShutdownRequest {
    calling_hart_id: usize,
}

impl ShutdownRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { calling_hart_id: confidential_hart.confidential_hart_id() }
    }

    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match ControlDataStorage::try_confidential_vm(confidential_flow.confidential_vm_id(), |confidential_vm| {
            confidential_flow.broadcast_remote_command(&confidential_vm, ConfidentialHartRemoteCommand::ShutdownRequest(self))
        }) {
            Ok(_) => shutdown_confidential_hart(confidential_flow),
            Err(error) => {
                confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(SbiResponse::error(error)))
            }
        }
    }

    pub fn is_hart_selected(&self, hart_id: usize) -> bool {
        self.calling_hart_id != hart_id
    }
}
