// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::interrupts::InterruptRequest;
use crate::confidential_flow::handlers::invalid_call::InvalidCall;
use crate::confidential_flow::handlers::mmio::load_request::MmioLoadRequest;
use crate::confidential_flow::handlers::mmio::store_request::MmioStoreRequest;
use crate::confidential_flow::handlers::mmio::{MmioLoadResult, MmioStoreResult};
use crate::confidential_flow::handlers::sbi::{SbiExtensionProbe, SbiRequest, SbiResult};
use crate::confidential_flow::handlers::shared_page::{SharePageRequest, SharePageResult, UnsharePageRequest};
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::smp::{
    NoOperation, SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartStop, SbiHsmHartSuspend, SbiIpi, SbiRemoteFenceI, SbiRemoteSfenceVma,
    SbiRemoteSfenceVmaAsid,
};
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstructionRequest;
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::BaseExtension::*;
use crate::core::architecture::HsmExtension::*;
use crate::core::architecture::IpiExtension::*;
use crate::core::architecture::RfenceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::SrstExtension::*;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{SbiExtension, TrapCause};
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ControlData, HardwareHart, HypervisorHart};
use crate::core::transformations::PendingRequest::*;
use crate::core::transformations::{DeclassifyToHypervisor, ExposeToConfidentialVm, InterHartRequest, PendingRequest};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

extern "C" {
    fn exit_to_confidential_hart_asm() -> !;
}

/// Ensures control flow integrity within the `confidential flow` part of the finite state machine (FSM) of the security
/// monitor.
///
/// The ConfidentialFlow has an ownership of the HardwareHart and a ConfidentialHart assigned to this hardware hart. It
/// encapsulates both HardwareHart and ConfidentialHart, so the only way to access their confidential state is through
/// ConfidentialFlow's public functions.
///
/// # Guarantees
///
/// * A confidential hart is assigned to the hardware hart.
/// * The confidential VM that logically owns the confidential hart exists in the control data.
pub struct ConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    /// Routes the control flow to a handler that will process the confidential hart interrupt or exception.
    ///
    /// Creates the mutable reference to HardwareHart by casting a raw pointer obtained from the context switch (assembly), see safety
    /// requirements of the asembly context switch. This is a private function, not accessible from the outside of the ConfidentialFlow but
    /// accessible to the assembly code performing the context switch.
    #[no_mangle]
    extern "C" fn route_confidential_flow(hardware_hart_pointer: *mut HardwareHart) -> ! {
        let hardware_hart = unsafe { hardware_hart_pointer.as_mut().expect(crate::error::CTX_SWITCH_ERROR_MSG) };
        assert!(!hardware_hart.confidential_hart().is_dummy());
        let mut flow = Self { hardware_hart };
        flow.confidential_hart_mut().csrs_mut().mepc.save();
        flow.confidential_hart_mut().csrs_mut().mstatus.save();

        match TrapCause::from_hart_architectural_state(flow.confidential_hart().confidential_hart_state()) {
            Interrupt => InterruptRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Ace(SharePageWithHypervisor)) => SharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Ace(StopSharingPageWithHypervisor)) => {
                UnsharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow)
            }
            VsEcall(Base(GetSpecVersion)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplId)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplVersion)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(ProbeExtension)) => SbiExtensionProbe::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMvendorId)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMarchid)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMimpid)) => SbiRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Ipi(SendIpi)) => SbiIpi::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteFenceI)) => SbiRemoteFenceI::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteSfenceVma)) => SbiRemoteSfenceVma::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteSfenceVmaAsid)) => SbiRemoteSfenceVmaAsid::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceGvmaVmid)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceGvma)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceVvmaAsid)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Rfence(RemoteHfenceVvma)) => NoOperation::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartStart)) => SbiHsmHartStart::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartStop)) => SbiHsmHartStop::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartSuspend)) => SbiHsmHartSuspend::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Hsm(HartGetStatus)) => SbiHsmHartStatus::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Srst(SystemReset)) => ShutdownRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(SbiExtension::Unknown(_, _)) => InvalidCall::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestLoadPageFault => MmioLoadRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VirtualInstruction => VirtualInstructionRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestStorePageFault => MmioStoreRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    /// This is an entry point to the confidential flow from the non-confidential flow.
    pub fn resume_confidential_hart_execution(hardware_hart: &'a mut HardwareHart) -> ! {
        assert!(!hardware_hart.confidential_hart().is_dummy());
        let mut flow = Self { hardware_hart };

        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // InterHartRequests. We must process them before resuming confidential hart's execution.
        flow.process_inter_hart_requests();

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a hypercall or MMIO
        // load) to the hypervisor. We must now handle the response. Otherwise we just resume confidential hart's execution.
        match flow.hardware_hart.confidential_hart_mut().take_request() {
            Some(SbiRequest()) => SbiResult::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            Some(MmioLoad(request)) => MmioLoadResult::from_hypervisor_hart(flow.hypervisor_hart(), request).handle(flow),
            Some(MmioStore(request)) => MmioStoreResult::from_pending(request).handle(flow),
            Some(SharePage(request)) => SharePageResult::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow, request),
            Some(SbiHsmHartStartPending()) => {
                flow.hardware_hart.confidential_hart_mut().transition_from_start_pending_to_started();
                flow.exit_to_confidential_hart(ExposeToConfidentialVm::Nothing())
            }
            None => flow.exit_to_confidential_hart(ExposeToConfidentialVm::Nothing()),
        }
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn exit_to_confidential_hart(mut self, transformation: ExposeToConfidentialVm) -> ! {
        match transformation {
            ExposeToConfidentialVm::SbiResult(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            ExposeToConfidentialVm::VirtualInstructionResult(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            ExposeToConfidentialVm::Nothing() => {}
        }
        let address = self.hardware_hart.confidential_hart_mut().address();
        // We must restore some control and status registers (CSRs) that might have changed during execution of the security monitor.
        // We call it here because it is just before exiting to the assembly context switch, so we are sure that these CSRs have their
        // final values.
        let interrupts = self.confidential_hart().csrs().hvip.read_value() | self.confidential_hart().csrs().vsip.read_value();
        self.confidential_hart().csrs().hvip.set(interrupts);
        self.confidential_hart().csrs().sscratch.set(address);
        self.confidential_hart().csrs().mstatus.restore();
        self.confidential_hart().csrs().mepc.restore();
        unsafe { exit_to_confidential_hart_asm() }
    }

    /// Moves in the finite state machine (FSM) from the confidential flow into non-confidential flow.
    pub fn into_non_confidential_flow(self, declassify: DeclassifyToHypervisor) -> NonConfidentialFlow<'a> {
        let confidential_vm_id = self.confidential_vm_id();
        ControlData::try_confidential_vm(confidential_vm_id, |mut confidential_vm| {
            confidential_vm.return_confidential_hart(self.hardware_hart, declassify);
            Ok(NonConfidentialFlow::create(self.hardware_hart))
        })
        // below unwrap is safe because we are in the confidential flow that guarantees that the confidential VM with
        // the given id exists in the control data.
        .unwrap()
    }
}

// ConfidentialFlow implementation that supports inter hart requests, including IPIs
impl<'a> ConfidentialFlow<'a> {
    /// Broadcasts the inter hart request to confidential harts of the currently executing confidential VM.
    ///
    /// Returns error if sending an IPI to other confidential hart failed or if there is too many pending IPI queued.
    pub fn broadcast_inter_hart_request(&mut self, inter_hart_request: InterHartRequest) -> Result<(), Error> {
        ControlData::try_confidential_vm_mut(self.confidential_vm_id(), |mut confidential_vm| {
            // Hack: For the time-being, we rely on the OpenSBI implementation of physical IPIs. To use OpenSBI functions we
            // must set the mscratch register to the value expected by OpenSBI. We do it here, because we have access to the `HardwareHart`
            // that knows the original value of the mscratch expected by OpenSBI.
            self.hardware_hart.swap_mscratch();
            let result = confidential_vm.broadcast_inter_hart_request(inter_hart_request);
            // We must revert the content of mscratch back to the value expected by our context switched.
            self.hardware_hart.swap_mscratch();
            result
        })
    }

    /// Processes pending requests from other confidential harts by applying the corresponding state transformation to
    /// this confidential hart.
    ///
    /// This function must only be called when the hypervisor requested resume of confidential hart's execution or when
    /// a hardware hart executing a confidential hart is interrupted with the inter-processor-interrupt (IPI).
    pub fn process_inter_hart_requests(&mut self) {
        ControlData::try_confidential_vm(self.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.try_inter_hart_requests(self.confidential_hart_id(), |ref mut inter_hart_requests| {
                inter_hart_requests.drain(..).for_each(|inter_hart_request| {
                    // The confidential flow has an ownership of the confidential hart because the confidential hart
                    // is assigned to the hardware hart.
                    self.hardware_hart.confidential_hart_mut().execute(&inter_hart_request);
                });
                Ok(())
            })
        })
        // below unwrap is safe because 1) the confidential_vm_id and confidential_hart_id are valid since we are in the
        // confidential flow of the finite state machine (FSM) that guarantees it and 2) the processing of inter hart
        // requests always succeeds.
        .unwrap();
    }
}

// ConfidentialFlow implementation that supports optional hart lifecycle transitions.
impl<'a> ConfidentialFlow<'a> {
    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn suspend_confidential_hart(&mut self, request: SbiHsmHartSuspend) -> Result<(), Error> {
        self.hardware_hart.confidential_hart_mut().transition_from_started_to_suspended(request)
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn stop_confidential_hart(&mut self) -> Result<(), Error> {
        self.hardware_hart.confidential_hart_mut().transition_from_started_to_stopped()
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn start_confidential_hart_after_suspend(&mut self) -> Result<(), Error> {
        self.hardware_hart.confidential_hart_mut().transition_from_suspended_to_started()
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn shutdown_confidential_hart(&mut self) {
        self.hardware_hart.confidential_hart_mut().transition_to_shutdown();
    }
}

impl<'a> ConfidentialFlow<'a> {
    pub fn confidential_vm_id(&'a self) -> ConfidentialVmId {
        self.hardware_hart.confidential_hart().confidential_vm_id().expect("Bug: found dummy hart instead of a confidential hart")
    }

    pub fn confidential_hart_id(&'a self) -> usize {
        self.hardware_hart.confidential_hart().confidential_hart_id()
    }

    pub fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        self.hardware_hart.confidential_hart_mut()
    }

    pub fn confidential_hart(&'a self) -> &ConfidentialHart {
        self.hardware_hart.confidential_hart()
    }

    pub fn hypervisor_hart(&'a self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }

    pub fn set_pending_request(self, request: PendingRequest) -> Self {
        if let Err(error) = self.hardware_hart.confidential_hart_mut().set_pending_request(request) {
            self.exit_to_confidential_hart(error.into_confidential_transformation());
        }
        self
    }
}
