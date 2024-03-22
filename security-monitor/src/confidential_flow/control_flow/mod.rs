// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::*;
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::BaseExtension::*;
use crate::core::architecture::HsmExtension::*;
use crate::core::architecture::IpiExtension::*;
use crate::core::architecture::RfenceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::SrstExtension::*;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{HartArchitecturalState, SbiExtension, TrapCause};
use crate::core::control_data::{ConfidentialHart, ConfidentialVmId, ControlData, HardwareHart};
use crate::core::transformations::PendingRequest::*;
use crate::core::transformations::{ExposeToConfidentialVm, InterHartRequest, PendingRequest};
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
        flow.confidential_hart_state_mut().csrs_mut().mepc.save();
        flow.confidential_hart_state_mut().csrs_mut().mstatus.save();

        match TrapCause::from_hart_architectural_state(flow.confidential_hart_state()) {
            Interrupt => required::handle_interrupt(flow),
            VsEcall(Ace(SharePageWithHypervisor)) => shared_page::request_shared_page(flow),
            VsEcall(Ace(StopSharingPageWithHypervisor)) => shared_page::unshare_page(flow),
            VsEcall(Base(GetSpecVersion)) => hypercall::make_sbi_call(flow),
            VsEcall(Base(GetImplId)) => hypercall::make_sbi_call(flow),
            VsEcall(Base(GetImplVersion)) => hypercall::make_sbi_call(flow),
            VsEcall(Base(ProbeExtension)) => required::probe_sbi_extensions(flow),
            VsEcall(Base(GetMvendorId)) => hypercall::make_sbi_call(flow),
            VsEcall(Base(GetMarchid)) => hypercall::make_sbi_call(flow),
            VsEcall(Base(GetMimpid)) => hypercall::make_sbi_call(flow),
            VsEcall(Ipi(SendIpi)) => smp::send_inter_hart_request(flow),
            VsEcall(Rfence(RemoteFenceI)) => smp::send_inter_hart_request(flow),
            VsEcall(Rfence(RemoteSfenceVma)) => smp::send_inter_hart_request(flow),
            VsEcall(Rfence(RemoteSfenceVmaAsid)) => smp::send_inter_hart_request(flow),
            VsEcall(Rfence(RemoteHfenceGvmaVmid)) => smp::no_operation(flow),
            VsEcall(Rfence(RemoteHfenceGvma)) => smp::no_operation(flow),
            VsEcall(Rfence(RemoteHfenceVvmaAsid)) => smp::no_operation(flow),
            VsEcall(Rfence(RemoteHfenceVvma)) => smp::no_operation(flow),
            VsEcall(Hsm(HartStart)) => smp::start_remote_hart(flow),
            VsEcall(Hsm(HartStop)) => smp::stop_hart(flow),
            VsEcall(Hsm(HartSuspend)) => smp::suspend_hart(flow),
            VsEcall(Hsm(HartGetStatus)) => smp::get_hart_status(flow),
            VsEcall(Srst(SystemReset)) => shutdown::shutdown_confidential_vm(flow),
            VsEcall(SbiExtension::Unknown(_, _)) => required::invalid_call(flow),
            GuestLoadPageFault => mmio::request_mmio_load(flow),
            VirtualInstruction => required::emulate_instruction(flow),
            GuestStorePageFault => mmio::request_mmio_store(flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    /// This is an entry point to the confidential flow from the non-confidential flow.
    pub fn resume_confidential_hart_execution(hardware_hart: &'a mut HardwareHart) -> ! {
        assert!(!hardware_hart.confidential_hart().is_dummy());
        let mut confidential_flow = Self { hardware_hart };

        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // InterHartRequests. We must process them before resuming confidential hart's execution.
        confidential_flow.process_inter_hart_requests();

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a hypercall or MMIO
        // load) to the hypervisor. We must now handle the response. Otherwise we just resume confidential hart's execution.
        match confidential_flow.hardware_hart.confidential_hart_mut().take_request() {
            Some(SbiRequest()) => hypercall::process_sbi_response(confidential_flow),
            Some(MmioLoad(request)) => mmio::handle_mmio_load_response(confidential_flow, request),
            Some(MmioStore(request)) => mmio::handle_mmio_store_response(confidential_flow, request),
            Some(SharePage(request)) => shared_page::share_page(confidential_flow, request),
            Some(SbiHsmHartStart()) => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiHsmHartStart()),
            Some(SbiHsmHartStartPending()) => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiHsmHartStartPending()),
            None => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::Resume()),
        }
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn exit_to_confidential_hart(self, transformation: ExposeToConfidentialVm) -> ! {
        let address = self.hardware_hart.confidential_hart_mut().apply(transformation);
        // We must restore some control and status registers (CSRs) that might have changed during execution of the security monitor.
        // We call it here because it is just before exiting to the assembly context switch, so we are sure that these CSRs have their
        // final values.
        let interrupts = self.confidential_hart_state().csrs().hvip.read_value() | self.confidential_hart_state().csrs().vsip.read_value();
        self.confidential_hart_state().csrs().hvip.set(interrupts);
        self.confidential_hart_state().csrs().sscratch.set(address);
        self.confidential_hart_state().csrs().mstatus.restore();
        self.confidential_hart_state().csrs().mepc.restore();
        unsafe { exit_to_confidential_hart_asm() }
    }

    /// Moves in the finite state machine (FSM) from the confidential flow into non-confidential flow.
    pub fn into_non_confidential_flow(self) -> NonConfidentialFlow<'a> {
        let confidential_vm_id = self.confidential_vm_id();
        ControlData::try_confidential_vm(confidential_vm_id, |mut confidential_vm| {
            confidential_vm.return_confidential_hart(self.hardware_hart);
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
                inter_hart_requests.drain(..).map(|inter_hart_request| inter_hart_request.into_expose_to_confidential_vm()).for_each(
                    |transformation| {
                        // The confidential flow has an ownership of the confidential hart because the confidential hart
                        // is assigned to the hardware hart.
                        self.hardware_hart.confidential_hart_mut().apply(transformation);
                    },
                );
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
    pub fn suspend_confidential_hart(&mut self, request: crate::core::transformations::SbiHsmHartSuspend) -> Result<(), Error> {
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

    pub fn confidential_hart(&'a self) -> &ConfidentialHart {
        self.hardware_hart.confidential_hart()
    }

    pub fn hardware_hart(&'a self) -> &HardwareHart {
        &self.hardware_hart
    }

    pub fn confidential_hart_state(&self) -> &HartArchitecturalState {
        self.hardware_hart.confidential_hart().confidential_hart_state()
    }
    pub fn confidential_hart_state_mut(&mut self) -> &mut HartArchitecturalState {
        self.hardware_hart.confidential_hart_mut().confidential_hart_state_mut()
    }

    pub fn is_confidential_hart_shutdown(&self) -> bool {
        use crate::core::architecture::HartLifecycleState;
        self.hardware_hart.confidential_hart().lifecycle_state() == &HartLifecycleState::Shutdown
    }

    pub fn set_pending_request(self, request: PendingRequest) -> Self {
        if let Err(error) = self.hardware_hart.confidential_hart_mut().set_pending_request(request) {
            self.exit_to_confidential_hart(error.into_confidential_transformation());
        }
        self
    }
}
