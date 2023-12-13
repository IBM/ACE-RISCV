// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::{ConfidentialVmId, ControlData, HardwareHart};
use crate::core::transformations::SbiExtension::*;
use crate::core::transformations::{AceExtension, BaseExtension, ExposeToConfidentialVm, PendingRequest};
use crate::non_confidential_flow::NonConfidentialFlow;

extern "C" {
    fn exit_to_confidential_vm_asm(confidential_hart_address: usize) -> !;
}

pub struct ConfidentialFlow<'a> {
    hart: &'a mut HardwareHart,
}

impl<'a> ConfidentialFlow<'a> {
    pub fn create(hart: &'a mut HardwareHart) -> Self {
        Self { hart }
    }

    pub fn route(self) -> ! {
        use crate::confidential_flow::handlers::*;
        use crate::core::transformations::TrapReason::*;

        let confidential_hart = self.hart.confidential_hart();
        match confidential_hart.trap_reason() {
            Interrupt => interrupt::handle(self),
            VsEcall(Ace(AceExtension::SharePageWithHypervisor)) => {
                share_page::handle(confidential_hart.share_page_request(), self)
            }
            VsEcall(Ace(_)) => invalid_call::handle(self),
            VsEcall(Base(BaseExtension::Unknown(_, _))) => invalid_call::handle(self),
            VsEcall(Base(_)) => hypercall::handle(confidential_hart.hypercall_request(), self),
            VsEcall(_) => hypercall::handle(confidential_hart.hypercall_request(), self),
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

    pub fn finish_request(self) -> ! {
        use crate::confidential_flow::handlers::*;
        use crate::core::transformations::PendingRequest::*;

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

    pub fn into_non_confidential_flow(self) -> NonConfidentialFlow<'a> {
        let id = self.confidential_vm_id();
        match ControlData::try_confidential_vm(id, |mut cvm| Ok(cvm.return_confidential_hart(self.hart))) {
            Ok(_) => NonConfidentialFlow::create(self.hart),
            Err(error) => self.exit_to_confidential_vm(error.into_confidential_transformation()),
        }
    }

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
