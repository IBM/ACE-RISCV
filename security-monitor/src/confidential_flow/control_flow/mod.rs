// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialVmId, ControlData, HardwareHart};
use crate::core::transformations::SbiExtension::*;
use crate::core::transformations::{ExposeToConfidentialVm, PendingRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

extern "C" {
    fn exit_to_confidential_vm_asm(confidential_hart_address: usize) -> !;
}

/// The token that ensures correct control flow integrity within the `confidential flow` part of the finite state
/// machine (FSM) of the security monitor.
pub struct ConfidentialFlow<'a> {
    hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    /// Creates the confidential flow token.
    pub fn create(hart: &'a mut HardwareHart) -> Self {
        Self { hart }
    }

    /// Routers the processing of confidential VM's trap to the responsible handler.
    pub fn route(self) -> ! {
        use crate::confidential_flow::handlers::*;
        use crate::core::transformations::AceExtension::*;
        use crate::core::transformations::BaseExtension::*;
        use crate::core::transformations::HsmExtension::*;
        use crate::core::transformations::IpiExtension::*;
        use crate::core::transformations::RfenceExtension::*;
        use crate::core::transformations::SrstExtension::*;
        use crate::core::transformations::TrapReason::*;

        let confidential_hart = self.hart.confidential_hart();
        match confidential_hart.trap_reason() {
            Interrupt => interrupt::handle(self),
            VsEcall(Ace(SharePageWithHypervisor)) => share_page::handle(confidential_hart.share_page_request(), self),
            VsEcall(Base(GetSpecVersion)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetImplId)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetImplVersion)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(ProbeExtension)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMvendorId)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMarchid)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Base(GetMimpid)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Rfence(RemoteFenceI)) => inter_hart_request::handle(confidential_hart.sbi_remote_fence_i(), self),
            VsEcall(Rfence(RemoteSfenceVma)) => {
                inter_hart_request::handle(confidential_hart.sbi_remote_sfence_vma(), self)
            }
            VsEcall(Rfence(RemoteSfenceVmaAsid)) => {
                inter_hart_request::handle(confidential_hart.sbi_remote_sfence_vma_asid(), self)
            }
            VsEcall(Rfence(_)) => invalid_call::handle(self),
            VsEcall(Hsm(HartStart)) => sbi_hsm_hart_start::handle(confidential_hart.sbi_hsm_hart_start(), self),
            VsEcall(Hsm(HartGetStatus)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(Ipi(SendIpi)) => inter_hart_request::handle(confidential_hart.sbi_ipi(), self),
            VsEcall(Srst(SystemReset)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(_) => invalid_call::handle(self),
            GuestLoadPageFault => {
                guest_load_page_fault::handle(confidential_hart.guest_load_page_fault_request(), self)
            }
            GuestStorePageFault => {
                guest_store_page_fault::handle(confidential_hart.guest_store_page_fault_request(), self)
            }
            HsEcall(_) => panic!("Bug: Incorrect interrupt delegation configuration"),
            StoreAccessFault => panic!("Bug: Incorrect interrupt delegation configuration"),
            _ => invalid_call::handle(self),
        }
    }

    /// Processes pending requests from other confidential harts by applying corresponding state transformation to this
    /// confidential hart. Returns error if it fails to access the shared state that stores InterHartRequests.
    ///
    /// InterHartRequests are applied on the confidential hart only when the hypervisor resumes execution of a
    /// confidential hart or when a hardware hart executing a confidential hart is interrupted with the
    /// inter-processor-interrupt (IPI).
    pub fn process_inter_hart_requests(&mut self) {
        let confidential_vm_id = self.confidential_vm_id();
        let confidential_hart_id = self.hart.confidential_hart().confidential_hart_id();
        ControlData::try_confidential_vm(confidential_vm_id, |confidential_vm| {
            confidential_vm.try_inter_hart_requests(confidential_hart_id, |ref mut inter_hart_requests| {
                inter_hart_requests
                    .drain(..)
                    .map(|inter_hart_request| inter_hart_request.into_expose_to_confidential_vm())
                    .for_each(|transformation| {
                        self.hart.confidential_hart_mut().apply(transformation);
                    });
                Ok(())
            })
        })
        // below unwrap is safe because the confidential_vm_id and confidential_hart_id are valid since we are in the
        // confidential flow of the finite state machine (FSM) that guarantees it.
        .unwrap();
    }

    /// Resumes execution of the confidential hart after the confidential hart was not running on any physical hart.
    pub fn resume_confidential_hart_execution(mut self) -> ! {
        use crate::confidential_flow::handlers::*;
        use crate::core::transformations::PendingRequest::*;

        // During the time when this confidential hart was not running, other confidential harts could have sent it
        // InterHartRequests. We must process them before resuming confidential hart's execution.
        self.process_inter_hart_requests();

        // One of the reasons why this confidential hart was not running is that it could have sent a request (e.g., a
        // hypercall) to the hypervisor. We must now handle the response or resume confidential hart's execution.
        match self.hart.confidential_hart_mut().take_request() {
            Some(SbiRequest()) => hypercall_result::handle(self.hart.hypercall_result(), self),
            Some(GuestLoadPageFault(request)) => {
                guest_load_page_fault_result::handle(self.hart.guest_load_page_fault_result(request), self)
            }
            Some(GuestStorePageFault(request)) => guest_store_page_fault_result::handle(self, request),
            Some(SharePage(request)) => share_page_result::handle(self.hart.share_page_result(), self, request),
            None => self.exit_to_confidential_vm(ExposeToConfidentialVm::Resume()),
        }
    }

    /// Moves in the finite state machine (FSM) from the confidential flow into non-confidential flow.
    pub fn into_non_confidential_flow(self) -> NonConfidentialFlow<'a> {
        let confidential_vm_id = self.confidential_vm_id();
        ControlData::try_confidential_vm(confidential_vm_id, |mut confidential_vm| {
            confidential_vm.return_confidential_hart(self.hart);
            Ok(NonConfidentialFlow::create(self.hart))
        })
        // below unwrap is safe because we are in the confidential flow that guarantees that the confidential VM with
        // the given id exists in the control data.
        .unwrap()
    }

    /// Applies transformation to the confidential hart and passes control to the context switch (assembly) that will
    /// execute the confidential hart on the hardware hart.
    pub fn exit_to_confidential_vm(self, transformation: ExposeToConfidentialVm) -> ! {
        let confidential_hart_address = self.hart.confidential_hart_mut().apply(transformation);
        unsafe { exit_to_confidential_vm_asm(confidential_hart_address) }
    }

    pub fn confidential_vm_id(&'a self) -> ConfidentialVmId {
        self.hart
            .confidential_hart()
            .confidential_vm_id()
            .expect("Bug: found dummy hart instead of a confidential hart")
    }

    pub fn set_pending_request(self, request: PendingRequest) -> Self {
        if let Err(error) = self.hart.confidential_hart_mut().set_pending_request(request) {
            self.exit_to_confidential_vm(error.into_confidential_transformation());
        }
        self
    }
}
