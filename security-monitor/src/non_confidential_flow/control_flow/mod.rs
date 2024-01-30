// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::control_data::{ControlData, HardwareHart};
use crate::core::transformations::{ExposeToHypervisor, ResumeRequest};
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
    /// Creates an instance of non-confidential flow token. NonConfidentialFlow instance can be created only by the code
    /// owning a mutable reference to the HardwareHart. This can be only the piece of code invoked by assembly and the
    /// ConfidentialFlow.
    ///
    /// Safety:
    /// * A confidential hart must be assigned to the hardware hart.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        assert!(hardware_hart.confidential_hart().is_dummy());
        Self { hardware_hart }
    }

    pub fn route(self) -> ! {
        use crate::core::architecture::TrapReason::*;
        use crate::non_confidential_flow::handlers::*;

        match self.hardware_hart.trap_reason() {
            Interrupt => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            VsEcall(Ace(ConvertToConfidentialVm)) => {
                convert_to_confidential_vm::handle(self.hardware_hart.convert_to_confidential_vm_request(), self)
            }
            VsEcall(_) => vm_hypercall::handle(self.hardware_hart.sbi_vm_request(), self),
            HsEcall(Ace(ResumeConfidentialHart)) => resume::handle(self.hardware_hart.resume_request(), self),
            HsEcall(Ace(TerminateConfidentialVm)) => terminate::handle(self.hardware_hart.terminate_request(), self),
            HsEcall(_) => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            StoreAccessFault => opensbi::handle(self.hardware_hart.opensbi_request(), self),
            GuestLoadPageFault => panic!("Bug: Incorrect interrupt delegation configuration"),
            GuestStorePageFault => panic!("Bug: Incorrect interrupt delegation configuration"),
            _ => invalid_call::handle(self),
        }
    }

    pub fn into_confidential_flow(self, resume_request: ResumeRequest) -> (NonConfidentialFlow<'a>, Error) {
        match ControlData::try_confidential_vm(resume_request.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.steal_confidential_hart(resume_request.confidential_hart_id(), self.hardware_hart)
        }) {
            Ok(()) => ConfidentialFlow::resume_confidential_hart_execution(self.hardware_hart),
            Err(error) => (self, error),
        }
    }

    pub fn exit_to_hypervisor(self, transformation: ExposeToHypervisor) -> ! {
        self.hardware_hart.apply(&transformation);
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Swaps the mscratch register value with the original mascratch value used by OpenSBI. This function must be
    /// called before executing any OpenSBI function. If we get rid of OpenSBI firmware, then we can remove this
    /// function.
    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }
}
