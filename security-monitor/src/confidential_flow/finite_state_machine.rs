// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::interrupts::{AllowExternalInterrupt, HandleInterrupt};
use crate::confidential_flow::handlers::invalid_call::InvalidCall;
use crate::confidential_flow::handlers::mmio::{
    AddMmioRegion, MmioLoadRequest, MmioLoadResponse, MmioStoreRequest, MmioStoreResponse, RemoveMmioRegion,
};
use crate::confidential_flow::handlers::sbi::{
    SbiExtensionProbe, SbiGetImplId, SbiGetImplVersion, SbiGetMarchId, SbiGetMimpid, SbiGetMvendorid, SbiGetSpecVersion, SbiResponse,
};
use crate::confidential_flow::handlers::shared_page::{SharePageRequest, SharePageResponse, UnsharePageRequest};
use crate::confidential_flow::handlers::shutdown::ShutdownRequest;
use crate::confidential_flow::handlers::smp::{
    NoOperation, SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartStop, SbiHsmHartSuspend, SbiIpi, SbiRemoteFenceI, SbiRemoteSfenceVma,
    SbiRemoteSfenceVmaAsid,
};
use crate::confidential_flow::handlers::virtual_instructions::VirtualInstruction;
use crate::confidential_flow::{ApplyToConfidentialHart, DeclassifyToConfidentialVm};
use crate::core::architecture::BaseExtension::*;
use crate::core::architecture::CovgExtension::*;
use crate::core::architecture::HsmExtension::*;
use crate::core::architecture::IpiExtension::*;
use crate::core::architecture::RfenceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::SrstExtension::*;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{CovgExtension, HartLifecycleState, SbiExtension, TrapCause};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialVmId, ControlData, HardwareHart, HypervisorHart, InterHartRequest, PendingRequest,
};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

extern "C" {
    fn exit_to_confidential_hart_asm() -> !;
}

/// Ensures control flow integrity within the `confidential flow` part of the finite state machine (FSM) of the security
/// monitor.
///
/// The ConfidentialFlow has an ownership of HypervisorHart and ConfidentialHart assigned to this physical hart. It
/// encapsulates both HypervisorHart and ConfidentialHart, so the only way to access their confidential state is through
/// ConfidentialFlow's public functions.
///
/// # Guarantees
///
/// * A confidential hart (not a dummy one!) is assigned to the hardware hart.
/// * The confidential VM that logically owns the confidential hart exists in the control data.
pub struct ConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    const CTX_SWITCH_ERROR_MSG: &'static str = "Bug: invalid argument provided by the assembly context switch";

    /// Routes the control flow to a handler that will process the confidential hart interrupt or exception. This is an entry point to
    /// the security monitor from the assembly context switch.
    ///
    /// Creates the mutable reference to HardwareHart by casting a raw pointer obtained from the context switch (assembly), see safety
    /// requirements of the asembly context switch. This is a private function, not accessible to the Rust code from the outside of the
    /// ConfidentialFlow but accessible to the assembly code performing the context switch.
    #[no_mangle]
    unsafe extern "C" fn route_trap_from_confidential_hart(hardware_hart_pointer: *mut HardwareHart) -> ! {
        let flow = Self { hardware_hart: unsafe { hardware_hart_pointer.as_mut().expect(Self::CTX_SWITCH_ERROR_MSG) } };
        assert!(!flow.hardware_hart.confidential_hart().is_dummy());
        let trap = TrapCause::from_hart_architectural_state(flow.confidential_hart().confidential_hart_state());
        // debug!("C trap: {:?}", trap);
        match trap {
            Interrupt => HandleInterrupt::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetSpecVersion)) => SbiGetSpecVersion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplId)) => SbiGetImplId::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetImplVersion)) => SbiGetImplVersion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(ProbeExtension)) => SbiExtensionProbe::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMvendorId)) => SbiGetMvendorid::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMarchid)) => SbiGetMarchId::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Base(GetMimpid)) => SbiGetMimpid::from_confidential_hart(flow.confidential_hart()).handle(flow),
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
            VsEcall(Covg(AddMmioRegion)) => AddMmioRegion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(RemoveMmioRegion)) => RemoveMmioRegion::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(AllowExternalInterrupt)) => AllowExternalInterrupt::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(ShareMemory)) => SharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(UnshareMemory)) => UnsharePageRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VsEcall(Covg(CovgExtension::Unknown(a, b))) => panic!("Not supported Covg call {:x} {:x}", a, b),
            VsEcall(SbiExtension::Unknown(_, _)) => InvalidCall::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestLoadPageFault => MmioLoadRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            VirtualInstruction => VirtualInstruction::from_confidential_hart(flow.confidential_hart()).handle(flow),
            GuestStorePageFault => MmioStoreRequest::from_confidential_hart(flow.confidential_hart()).handle(flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    /// Creates an instance of the confidential flow for the requested confidential hart. Returns error if it cannot steal the confidental
    /// hart, i.e., the confidential hart does not exist or it has been already assigned another physical hart.
    pub fn enter_from_non_confidential_flow(
        hardware_hart: &'a mut HardwareHart, confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize,
    ) -> Result<Self, (&'a mut HardwareHart, Error)> {
        assert!(hardware_hart.confidential_hart().is_dummy());
        match ControlData::try_confidential_vm(confidential_vm_id, |mut confidential_vm| {
            confidential_vm.steal_confidential_hart(confidential_hart_id, hardware_hart)
        }) {
            Ok(_) => Ok(Self { hardware_hart }),
            Err(error) => Err((hardware_hart, error)),
        }
    }

    /// Moves in the finite state machine (FSM) from the confidential flow into non-confidential flow.
    pub fn into_non_confidential_flow(self) -> NonConfidentialFlow<'a> {
        ControlData::try_confidential_vm(self.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.return_confidential_hart(self.hardware_hart);
            Ok(NonConfidentialFlow::create(self.hardware_hart))
        })
        // below unwrap is safe because we are in the confidential flow that guarantees that the confidential VM with
        // the given id exists in the control data.
        .unwrap()
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    /// This is an entry point to the confidential flow from the non-confidential flow.
    pub fn resume_confidential_hart_execution(mut self) -> ! {
        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // InterHartRequests. We must process them before resuming confidential hart's execution.
        self.process_inter_hart_requests();

        // It might have happened, that this confidential hart has been shutdown when processing an IPI. I.e., there was
        // an IPI from other confidential hart that requested this confidential hart to shutdown. If this had happened, we
        // cannot resume this confidential hart anymore. We must exit to the hypervisor and inform it about it.
        if self.confidential_hart().lifecycle_state() == &HartLifecycleState::Shutdown {
            crate::confidential_flow::handlers::shutdown::shutdown_confidential_hart(self);
        }

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a hypercall or MMIO
        // load) to the hypervisor. We must now handle the response. Otherwise we just resume confidential hart's execution.
        use crate::core::control_data::PendingRequest::*;
        match self.confidential_hart_mut().take_request() {
            Some(SbiRequest()) => SbiResponse::from_hypervisor_hart(self.hypervisor_hart()).handle(self),
            Some(MmioLoad(request)) => MmioLoadResponse::from_hypervisor_hart(self.hypervisor_hart(), request).handle(self),
            Some(MmioStore(request)) => MmioStoreResponse::from_hypervisor_hart(self.hypervisor_hart(), request).handle(self),
            Some(SharePage(request)) => SharePageResponse::from_hypervisor_hart(self.hypervisor_hart(), request).handle(self),
            None => self.exit_to_confidential_hart(),
        }
    }

    pub fn declassify_and_exit_to_confidential_hart(mut self, declassifier: DeclassifyToConfidentialVm) -> ! {
        match declassifier {
            DeclassifyToConfidentialVm::SbiResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            DeclassifyToConfidentialVm::MmioLoadResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
            DeclassifyToConfidentialVm::MmioStoreResponse(v) => v.declassify_to_confidential_hart(self.confidential_hart_mut()),
        }
        self.exit_to_confidential_hart()
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn apply_and_exit_to_confidential_hart(mut self, transformation: ApplyToConfidentialHart) -> ! {
        match transformation {
            ApplyToConfidentialHart::SbiResponse(v) => v.apply_to_confidential_hart(self.confidential_hart_mut()),
            ApplyToConfidentialHart::VirtualInstruction(v) => v.apply_to_confidential_hart(self.confidential_hart_mut()),
        }
        self.exit_to_confidential_hart()
    }

    fn exit_to_confidential_hart(mut self) -> ! {
        // We must restore some control and status registers (CSRs) that might have changed during execution of the security monitor.
        // We call it here because it is just before exiting to the assembly context switch, so we are sure that these CSRs have their
        // final values.
        let interrupts = self.confidential_hart().csrs().hvip.read_value() | self.confidential_hart().csrs().vsip.read_value();
        let address = self.confidential_hart_mut().address();
        self.confidential_hart().csrs().hvip.set(interrupts);
        self.confidential_hart().csrs().sscratch.set(address);
        unsafe { exit_to_confidential_hart_asm() }
    }
}

// ConfidentialFlow implementation that supports inter hart requests, including IPIs
impl<'a> ConfidentialFlow<'a> {
    /// Broadcasts the inter hart request to confidential harts of the currently executing confidential VM. Returns error if sending an IPI
    /// to other confidential hart failed or if there is too many pending IPI queued.
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
    fn process_inter_hart_requests(&mut self) {
        ControlData::try_confidential_vm(self.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.try_inter_hart_requests(self.confidential_hart_id(), |ref mut inter_hart_requests| {
                inter_hart_requests.drain(..).for_each(|inter_hart_request| {
                    // The confidential flow has an ownership of the confidential hart because the confidential hart
                    // is assigned to the hardware hart.
                    self.confidential_hart_mut().execute(&inter_hart_request);
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
        self.confidential_hart_mut().transition_from_started_to_suspended(request)
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn stop_confidential_hart(&mut self) -> Result<(), Error> {
        self.confidential_hart_mut().transition_from_started_to_stopped()
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn start_confidential_hart_after_suspend(&mut self) -> Result<(), Error> {
        self.confidential_hart_mut().transition_from_suspended_to_started()
    }

    /// Delegation of state transition to the confidential hart. The confidential hart is intentionally encapsulated to prevent access to it
    /// other than via the ControlFlow.
    pub fn shutdown_confidential_hart(&mut self) {
        self.confidential_hart_mut().transition_to_shutdown();
    }
}

impl<'a> ConfidentialFlow<'a> {
    pub fn set_pending_request(mut self, request: PendingRequest) -> Self {
        if let Err(error) = self.confidential_hart_mut().set_pending_request(request) {
            self.apply_and_exit_to_confidential_hart(error.into_confidential_transformation());
        }
        self
    }

    pub fn confidential_vm_id(&'a self) -> ConfidentialVmId {
        self.confidential_hart().confidential_vm_id().expect("Bug: found dummy hart instead of a confidential hart")
    }

    fn confidential_hart_id(&'a self) -> usize {
        self.confidential_hart().confidential_hart_id()
    }

    fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        self.hardware_hart.confidential_hart_mut()
    }

    fn confidential_hart(&'a self) -> &ConfidentialHart {
        self.hardware_hart.confidential_hart()
    }

    fn hypervisor_hart(&'a self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }
}
