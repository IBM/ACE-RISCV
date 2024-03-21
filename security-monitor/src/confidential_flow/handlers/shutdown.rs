// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::ControlData;
use crate::core::transformations::{ExposeToHypervisor, InterHartRequest, SbiRequest, SbiSrstSystemReset};

/// Handles the system reset call of the SBI's SRST extension. This call is a request to shutdown or reboot the
/// confidential virtual machine. The security monitor allows only for the full shutdown of the confidential virtual
/// machine and thus, it treats every call to this function as a VM shutdown.
///
/// To shutdown the entire confidential VM and remove it from the control data memory, all confidential harts must be
/// shutdown (lifecycle state `Shutdown`). To do so, we send `Shutdown IPI` to all confidential harts. The last
/// confidential hart that shutdowns itself, will remove the entire confidential VM from the control data.
pub fn shutdown_confidential_vm(mut confidential_flow: ConfidentialFlow) -> ! {
    let confidential_hart_id = confidential_flow.confidential_hart_id();
    let shutdown_ipi = InterHartRequest::SbiSrstSystemReset(SbiSrstSystemReset::new(confidential_hart_id));
    match confidential_flow.broadcast_inter_hart_request(shutdown_ipi) {
        Ok(_) => shutdown_confidential_hart(confidential_flow),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}

/// Shuts down the currently executing confidential hart (and the corresponding confidential VM, if possible).
/// After cleaning up, this functions passes the control to the hypervisor informing it that the confidential VM has
/// been shutdown.
///
/// Always returns the control flow to the hypervisor informing it about the shutdown of the confidential VM.
pub fn shutdown_confidential_hart(mut confidential_flow: ConfidentialFlow) -> ! {
    let confidential_vm_id = confidential_flow.confidential_vm_id();
    // change the lifecycle status of the confidential hart to Shutdown
    confidential_flow.shutdown_confidential_hart();
    // The procedure of removing the confidential VM from the control data must be handled in the non-confidential flow
    // because all confidential harts must be released back to the control data.
    let non_confidential_flow = confidential_flow.into_non_confidential_flow();
    let _ = ControlData::remove_confidential_vm(confidential_vm_id);
    // We ignore the result of removing the confidential vm from the control data because it will return an error as
    // long as all confidential harts are in the `Shutdown` state. We do not know which confidential hart will be the
    // last one to shutdown, so we always try to remove the confidential VM when a confidential hart goes through the
    // shutdown procedure.
    non_confidential_flow.exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_srst_system_reset()))
}
