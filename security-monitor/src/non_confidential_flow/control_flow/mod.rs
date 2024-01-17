// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::{ControlData, HardwareHart};
use crate::core::transformations::SbiExtension::*;
use crate::core::transformations::{AceExtension, ExposeToHypervisor, ResumeRequest};
use crate::error::Error;

extern "C" {
    // TODO: To ensure safety, specify all possible valid states that KVM expects to see and prove that security monitor
    // never returns to KVM with other state. For example, only a subset of exceptions/interrupts can be handled by KVM.
    // KVM kill the vcpu if it receives unexpected exception because it does not know what to do with it.
    fn exit_to_hypervisor_asm() -> !;
}

/// This control flow structure acts like a wrapper around HardwareHart. HardwareHart is never exposed
pub struct NonConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> NonConfidentialFlow<'a> {
    /// This token can be created only by the code owning a mutable reference to
    /// the HardwareHart. This can be only the router and the ConfidentialFlow.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        Self { hardware_hart }
    }

    pub fn into_confidential_flow(
        self, resume_request: ResumeRequest,
    ) -> Result<ConfidentialFlow<'a>, (NonConfidentialFlow<'a>, Error)> {
        let confidential_vm_id = resume_request.confidential_vm_id();
        let confidential_hart_id = resume_request.confidential_hart_id();
        match ControlData::try_confidential_vm(confidential_vm_id, |mut confidential_vm| {
            confidential_vm.steal_confidential_hart(confidential_hart_id, self.hardware_hart)
        }) {
            Ok(()) => Ok(ConfidentialFlow::create(self.hardware_hart)),
            Err(error) => Err((self, error)),
        }
    }

    pub fn route(self) -> ! {
        use crate::core::transformations::TrapReason::*;
        use crate::non_confidential_flow::handlers::*;

        match self.hardware_hart.trap_reason() {
            Interrupt => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            VsEcall(Ace(AceExtension::ConvertToConfidentialVm)) => {
                convert_to_confidential_vm::handle(self.hardware_hart.convert_to_confidential_vm_request(), self)
            }
            VsEcall(_) => vm_hypercall::handle(self.hardware_hart.sbi_vm_request(), self),
            HsEcall(Ace(AceExtension::ResumeConfidentialHart)) => {
                resume::handle(self.hardware_hart.resume_request(), self)
            }
            HsEcall(Ace(AceExtension::TerminateConfidentialVm)) => {
                terminate::handle(self.hardware_hart.terminate_request(), self)
            }
            HsEcall(_) => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            StoreAccessFault => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            GuestLoadPageFault => panic!("Bug: Incorrect interrupt delegation configuration"),
            GuestStorePageFault => panic!("Bug: Incorrect interrupt delegation configuration"),
            _ => invalid_call::handle(self),
        }
    }

    pub fn exit_to_hypervisor(self, transformation: ExposeToHypervisor) -> ! {
        self.hardware_hart.apply(&transformation);
        unsafe { exit_to_hypervisor_asm() }
    }

    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }
}
