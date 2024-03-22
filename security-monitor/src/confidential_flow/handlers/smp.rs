// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::TrapCause;
use crate::core::control_data::ControlData;
use crate::core::transformations::{
    ExposeToConfidentialVm, ExposeToHypervisor, InterHartRequest, PendingRequest, SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartSuspend,
    SbiRequest, SbiResult,
};

/// Requests to start a remote confidential hart. This is an implementation of the HartStart function from the HSM extension of SBI.
///
/// This call is triggered by a confidential hart that wants to start another confidential hart. Error is returned to
/// the caller if the targetted confidential hart is not in the stopped state or it does not exist. The security monitor
/// moves targetted confidential harts into `StartPending` state and informs then the hypervisor that these harts are
/// runnable. Once the hypervisor schedules such a confidential hart for execution, the confidential hart will change
/// the state to `Started`.
pub fn start_remote_hart(confidential_flow: ConfidentialFlow) -> ! {
    let request = SbiHsmHartStart::from_confidential_hart(confidential_flow.confidential_hart());
    let confidential_hart_id = request.confidential_hart_id();
    // We expect the confidential hart to be inside the control data (not assigned to a hardware hart), otherwise there is no need to start
    // this confidential hart.
    match ControlData::try_confidential_vm_mut(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
        confidential_vm.transit_confidential_hart_to_start_pending(request)
    }) {
        Ok(_) => confidential_flow
            .set_pending_request(PendingRequest::SbiHsmHartStart())
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_start(confidential_hart_id))),
        Err(error) => {
            // starting a confidential hart might fail if the incoming request is invalid. For example, the confidential
            // hart id does not exist or is the same as the one currently assigned to the hardware hart. In such cases,
            // return an error to the calling confidential hart.
            confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation());
        }
    }
}

/// Returns the lifecycle state of the confidential hart as defined in the HART get status (FID #2) function of the SBI's HSM extension.
pub fn get_hart_status(confidential_flow: ConfidentialFlow) -> ! {
    let request = SbiHsmHartStatus::from_confidential_hart(confidential_flow.confidential_hart());
    let transformation = ControlData::try_confidential_vm(confidential_flow.confidential_vm_id(), |ref mut confidential_vm| {
        confidential_vm.confidential_hart_lifecycle_state(request.confidential_hart_id())
    })
    .and_then(|lifecycle_state| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(lifecycle_state.sbi_code()))))
    .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_hart(transformation)
}

/// Stops the confidential hart as defined in the HSM extension of SBI. Error is returned to the confidential hart if
/// the security monitor cannot stop it, for example, because it is not in the started state.
///
/// The request to stop the confidential hart comes from the confidential hart itself. The security monitor stops the
/// hart and informs the hypervisor that the hart has been stopped. The hypervisor should not resume execution of a
/// stopped confidential hart. Only another confidential hart of the confidential VM can start the confidential hart.
pub fn stop_hart(mut confidential_flow: ConfidentialFlow) -> ! {
    match confidential_flow.stop_confidential_hart() {
        Ok(_) => confidential_flow
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_stop())),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}

/// Suspends a confidential hart that made this request. This is an implementation of the HartSuspend function from the
/// HSM extension of SBI.
///
/// The request to suspend the confidential hart comes frmo the confidential hart itself. The security monitor suspends
/// the confidential hart and informs about it the hypervisor. This functions returns an error to the calling
/// confidential hart if this confidential hart cannot be suspended, for example, because it is not in the started
/// state.
pub fn suspend_hart(mut confidential_flow: ConfidentialFlow) -> ! {
    let request = SbiHsmHartSuspend::from_confidential_hart(confidential_flow.confidential_hart());
    match confidential_flow.suspend_confidential_hart(request) {
        Ok(_) => confidential_flow
            .into_non_confidential_flow()
            .exit_to_hypervisor(ExposeToHypervisor::SbiRequest(SbiRequest::kvm_hsm_hart_suspend())),
        Err(error) => confidential_flow.exit_to_confidential_hart(error.into_confidential_transformation()),
    }
}

/// Injects an InterHartRequest to confidential harts specified as part of the request.
pub fn send_inter_hart_request(mut confidential_flow: ConfidentialFlow) -> ! {
    use crate::core::architecture::IpiExtension::*;
    use crate::core::architecture::RfenceExtension::*;
    use crate::core::architecture::SbiExtension::{Ipi, Rfence};
    use crate::core::architecture::TrapCause::VsEcall;
    use crate::core::transformations::{SbiIpi, SbiRemoteFenceI, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid};

    let confidential_hart = confidential_flow.confidential_hart();
    let request = match TrapCause::from_hart_architectural_state(confidential_flow.confidential_hart_state()) {
        VsEcall(Ipi(SendIpi)) => InterHartRequest::SbiIpi(SbiIpi::from_confidential_hart(confidential_hart)),
        VsEcall(Rfence(RemoteFenceI)) => InterHartRequest::SbiRemoteFenceI(SbiRemoteFenceI::from_confidential_hart(confidential_hart)),
        VsEcall(Rfence(RemoteSfenceVma)) => {
            InterHartRequest::SbiRemoteSfenceVma(SbiRemoteSfenceVma::from_confidential_hart(confidential_hart))
        }
        VsEcall(Rfence(RemoteSfenceVmaAsid)) => {
            InterHartRequest::SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid::from_confidential_hart(confidential_hart))
        }
        _ => panic!("incorrect delegation setup"),
    };

    let transformation = confidential_flow
        .broadcast_inter_hart_request(request.clone())
        .and_then(|_| Ok(ExposeToConfidentialVm::SbiResult(SbiResult::success(0))))
        .unwrap_or_else(|error| error.into_confidential_transformation());

    confidential_flow.exit_to_confidential_hart(transformation)
}

/// Implements NOP (no operation) for calls that are not implemented by the security monitor but should be supported due to compatibility
/// reasons. These calls are remote fence SBI calls required in systems supporting nested virtualization.
pub fn no_operation(confidential_flow: ConfidentialFlow) -> ! {
    confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiResult(SbiResult::success(0)))
}
