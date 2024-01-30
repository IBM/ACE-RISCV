// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{InterHartRequest, SbiSrstSystemReset};

/// Handles the system reset call of the SBI's SRST extension. This call is a request to shutdown or reboot the
/// confidential virtual machine. The security monitor allows only for the full shutdown of the confidential virtual
/// machine and thus, it treats every call to this function as a VM shutdown.
///
/// To shutdown the entire confidential VM and remove it from the control data memory, all confidential harts must be
/// shutdown (lifecycle state `Shutdown`). To do so, we send `Shutdown IPI` to all confidential harts. The last
/// confidential hart that shutdowns itself, will remove the entire confidential VM from the control data.
pub fn handle(mut confidential_flow: ConfidentialFlow) -> ! {
    let confidential_hart_id = confidential_flow.confidential_hart_id();
    let shutdown_ipi = InterHartRequest::SbiSrstSystemReset(SbiSrstSystemReset::new(confidential_hart_id));
    match confidential_flow.broadcast_inter_hart_request(shutdown_ipi) {
        Ok(_) => crate::confidential_flow::handlers::shutdown_confidential_hart::handle(confidential_flow),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}
