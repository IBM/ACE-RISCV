// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart;
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ConfidentialHart;
use crate::core::transformations::InterHartRequest;

#[derive(PartialEq, Debug, Clone)]
pub struct ShutdownRequest {
    initiating_confidential_hart_id: usize,
}

impl ShutdownRequest {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self { initiating_confidential_hart_id: confidential_hart.confidential_hart_id() }
    }

    /// Handles the system reset call of the SBI's SRST extension. This call is a request to shutdown or reboot the
    /// confidential virtual machine. The security monitor allows only for the full shutdown of the confidential virtual
    /// machine and thus, it treats every call to this function as a VM shutdown.
    ///
    /// To shutdown the entire confidential VM and remove it from the control data memory, all confidential harts must be
    /// shutdown (lifecycle state `Shutdown`). To do so, we send `Shutdown IPI` to all confidential harts. The last
    /// confidential hart that shutdowns itself, will remove the entire confidential VM from the control data.
    pub fn handle(self, mut confidential_flow: ConfidentialFlow) -> ! {
        match confidential_flow.broadcast_inter_hart_request(InterHartRequest::ShutdownRequest(self)) {
            Ok(_) => shutdown_confidential_hart(confidential_flow),
            Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
        }
    }

    pub fn initiating_confidential_hart_id(&self) -> usize {
        self.initiating_confidential_hart_id
    }
}
