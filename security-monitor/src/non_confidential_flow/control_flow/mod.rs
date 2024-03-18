// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::TrapCause::*;
use crate::core::control_data::{ControlData, HardwareHart};
use crate::core::transformations::{ExposeToHypervisor, ResumeRequest};
use crate::error::Error;
use crate::non_confidential_flow::handlers::*;

extern "C" {
    /// To ensure safety, specify all possible valid states that KVM expects to see and prove that security monitor
    /// never returns to KVM with other state. For example, only a subset of exceptions/interrupts can be handled by KVM.
    /// KVM kill the vcpu if it receives unexpected exception because it does not know what to do with it.
    fn exit_to_hypervisor_asm() -> !;
}

/// This control flow structure encapsulates the HardwareHart instance, which is never exposed.
pub struct NonConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> NonConfidentialFlow<'a> {
    /// Creates an instance of non-confidential flow token. NonConfidentialFlow instance can be created only by the code
    /// owning a mutable reference to the HardwareHart. This can be only the piece of code invoked by assembly and the
    /// ConfidentialFlow.
    ///
    /// # Safety
    ///
    /// A confidential hart must be assigned to the hardware hart.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        assert!(hardware_hart.confidential_hart().is_dummy());
        Self { hardware_hart }
    }

    #[no_mangle]
    extern "C" fn route_non_confidential_flow(hart_ptr: *mut HardwareHart) -> ! {
        let hardware_hart = unsafe { hart_ptr.as_mut().expect(crate::error::CTX_SWITCH_ERROR_MSG) };
        hardware_hart.save_volatile_control_status_registers_in_main_memory();
        let control_flow = Self::create(hardware_hart);

        match control_flow.hardware_hart.trap_reason() {
            Interrupt => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            IllegalInstruction => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            LoadAddressMisaligned => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            LoadAccessFault => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            StoreAddressMisaligned => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            StoreAccessFault => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            HsEcall(Ace(ResumeConfidentialHart)) => {
                resume_confidential_hart::handle(control_flow.hardware_hart.resume_request(), control_flow)
            }
            HsEcall(Ace(TerminateConfidentialVm)) => {
                terminate_confidential_vm::handle(control_flow.hardware_hart.terminate_request(), control_flow)
            }
            HsEcall(_) => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            VsEcall(Ace(PromoteToConfidentialVm)) => {
                promote_to_confidential_vm::handle(control_flow.hardware_hart.promote_to_confidential_vm_request(), control_flow)
            }
            VsEcall(_) => delegate_hypercall::handle(control_flow.hardware_hart.sbi_vm_request(), control_flow),
            MachineEcall => delegate_to_opensbi::handle(control_flow.hardware_hart.opensbi_request(), control_flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    pub fn into_confidential_flow(self, resume_request: ResumeRequest) -> (NonConfidentialFlow<'a>, Error) {
        match ControlData::try_confidential_vm(resume_request.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.steal_confidential_hart(resume_request.confidential_hart_id(), self.hardware_hart)
        }) {
            Ok(_) => ConfidentialFlow::resume_confidential_hart_execution(self.hardware_hart),
            Err(error) => (self, error),
        }
    }

    pub fn exit_to_hypervisor(self, transformation: ExposeToHypervisor) -> ! {
        self.hardware_hart.apply(&transformation);
        self.hardware_hart.restore_volatile_control_status_registers_from_main_memory();
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Swaps the mscratch register value with the original mascratch value used by OpenSBI. This function must be
    /// called before executing any OpenSBI function. We can remove this once we get rid of the OpenSBI firmware.
    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }
}
