// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::SbiExtension::*;
use crate::core::control_data::{ConfidentialVmId, ControlData, HardwareHart};
use crate::core::transformations::{ExposeToConfidentialVm, InterHartRequest, PendingRequest};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;

extern "C" {
    fn exit_to_confidential_hart_asm(confidential_hart_address: usize) -> !;
}

/// Ensures control flow integrity within the `confidential flow` part of the finite state machine (FSM) of the security
/// monitor.
///
/// The ConfidentialFlow has an ownership of the HardwareHart and a ConfidentialHart assigned to this hardware hart. It
/// encapsulates both HardwareHart and ConfidentialHart, so the only way to access their confidential state is through
/// ConfidentialFlow's public functions.
///
/// Guarantees:
/// - A confidential hart is assigned to the hardware hart.
/// - The confidential VM that logically owns the confidential hart exists in the control data.
pub struct ConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    /// Creates an instance of the confidential flow.
    ///
    /// Safety:
    /// * A confidential hart must be assigned to the hardware hart.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        // TODO: make this constructor private, only accessible to this module and the assembly entry point.
        assert!(!hardware_hart.confidential_hart().is_dummy());
        Self { hardware_hart }
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

    /// Routes the control flow to a handler that will process the confidential hart interrupt or exception.
    pub fn route(self) -> ! {
        use crate::confidential_flow::handlers::*;
        use crate::core::architecture::AceExtension::*;
        use crate::core::architecture::BaseExtension::*;
        use crate::core::architecture::HsmExtension::*;
        use crate::core::architecture::IpiExtension::*;
        use crate::core::architecture::RfenceExtension::*;
        use crate::core::architecture::SrstExtension::*;
        use crate::core::architecture::TrapReason::*;

        let confidential_hart = self.hardware_hart.confidential_hart();
        match confidential_hart.trap_reason() {
            Interrupt => interrupt::handle(self),
            VsEcall(Ace(SharePageWithHypervisor)) => share_page::handle(confidential_hart.share_page_request(), self),
            VsEcall(Ace(StopSharingPageWithHypervisor)) => unshare_page::handle(confidential_hart.unshare_page_request(), self),
            VsEcall(Base(GetSpecVersion)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetImplId)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetImplVersion)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(ProbeExtension)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMvendorId)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMarchid)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMimpid)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Ipi(SendIpi)) => sbi_ipi::handle(confidential_hart.sbi_ipi(), self),
            VsEcall(Rfence(RemoteFenceI)) => sbi_ipi::handle(confidential_hart.sbi_remote_fence_i(), self),
            VsEcall(Rfence(RemoteSfenceVma)) => sbi_ipi::handle(confidential_hart.sbi_remote_sfence_vma(), self),
            VsEcall(Rfence(RemoteSfenceVmaAsid)) => sbi_ipi::handle(confidential_hart.sbi_remote_sfence_vma_asid(), self),
            VsEcall(Rfence(RemoteHfenceGvmaVmid)) => sbi_rfence_nop::handle(self),
            VsEcall(Rfence(RemoteHfenceGvma)) => sbi_rfence_nop::handle(self),
            VsEcall(Rfence(RemoteHfenceVvmaAsid)) => sbi_rfence_nop::handle(self),
            VsEcall(Rfence(RemoteHfenceVvma)) => sbi_rfence_nop::handle(self),
            VsEcall(Hsm(HartStart)) => sbi_hsm_hart_start::handle(confidential_hart.sbi_hsm_hart_start(), self),
            VsEcall(Hsm(HartStop)) => sbi_hsm_hart_stop::handle(self),
            VsEcall(Hsm(HartSuspend)) => sbi_hsm_hart_suspend::handle(confidential_hart.sbi_hsm_hart_suspend(), self),
            VsEcall(Hsm(HartGetStatus)) => sbi_hsm_hart_status::handle(confidential_hart.sbi_hsm_hart_status(), self),
            VsEcall(Srst(SystemReset)) => sbi_srst::handle(self),
            VsEcall(_) => invalid_call::handle(self),
            GuestLoadPageFault => guest_load_page_fault::handle(confidential_hart.guest_load_page_fault_request(), self),
            GuestStorePageFault => guest_store_page_fault::handle(confidential_hart.guest_store_page_fault_request(), self),
            _ => panic!("Bug: Incorrect interrupt delegation configuration"),
        }
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    /// This is an entry point to the confidential flow from the non-confidential flow.
    pub fn resume_confidential_hart_execution(hardware_hart: &'a mut HardwareHart) -> ! {
        let mut confidential_flow = Self::create(hardware_hart);

        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // InterHartRequests. We must process them before resuming confidential hart's execution.
        confidential_flow.process_inter_hart_requests();

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a
        // hypercall) to the hypervisor. We must now handle the response. Otherwise we just resume confidential hart's
        // execution.
        use crate::confidential_flow::handlers::*;
        use crate::core::transformations::PendingRequest::*;
        match confidential_flow.hardware_hart.confidential_hart_mut().take_request() {
            Some(SbiRequest()) => hypercall_result::handle(confidential_flow.hardware_hart.hypercall_result(), confidential_flow),
            Some(GuestLoadPageFault(request)) => guest_load_page_fault_result::handle(
                confidential_flow.hardware_hart.guest_load_page_fault_result(request),
                confidential_flow,
            ),
            Some(GuestStorePageFault(request)) => guest_store_page_fault_result::handle(confidential_flow, request),
            Some(SharePage(request)) => {
                share_page_result::handle(confidential_flow.hardware_hart.share_page_result(), confidential_flow, request)
            }
            Some(SbiHsmHartStart()) => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiHsmHartStart()),
            Some(SbiHsmHartStartPending()) => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::SbiHsmHartStartPending()),
            None => confidential_flow.exit_to_confidential_hart(ExposeToConfidentialVm::Resume()),
        }
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn exit_to_confidential_hart(self, transformation: ExposeToConfidentialVm) -> ! {
        let confidential_hart_address = self.hardware_hart.confidential_hart_mut().apply(transformation);
        unsafe { exit_to_confidential_hart_asm(confidential_hart_address) }
    }
}

// ConfidentialFlow implementation that supports inter hart requests, including IPIs
impl<'a> ConfidentialFlow<'a> {
    /// Broadcasts the inter hart request to confidential harts of the currently executing confidential VM.
    ///
    /// Returns error if sending an IPI to other confidential hart failed or if there is too many pending IPI queued.
    pub fn broadcast_inter_hart_request(&mut self, inter_hart_request: InterHartRequest) -> Result<(), Error> {
        ControlData::try_confidential_vm_mut(self.confidential_vm_id(), |mut confidential_vm| {
            // for the time-being, we rely on the OpenSBI implementation of physical IPIs. To use OpenSBI functions we
            // must set the mscratch register to the value expected by OpenSBI.
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
                        // is assigned to the hardware hart. This is why it is the confidential hart who processes inter
                        // hart requests and not the confidential VM.
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
