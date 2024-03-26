// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::TrapCause;
use crate::core::architecture::TrapCause::*;
use crate::core::control_data::{ControlData, HardwareHart, HypervisorHart};
use crate::core::transformations::ExposeToHypervisor;
use crate::error::Error;
use crate::non_confidential_flow::handlers::delegate_hypercall::SbiVmRequest;
use crate::non_confidential_flow::handlers::delegate_to_opensbi::OpensbiRequest;
use crate::non_confidential_flow::handlers::promote_to_confidential_vm::PromoteToConfidentialVm;
use crate::non_confidential_flow::handlers::resume_confidential_hart::ResumeRequest;
use crate::non_confidential_flow::handlers::terminate_confidential_vm::TerminateRequest;

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
    /// A confidential hart must not be assigned to the hardware hart.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        assert!(hardware_hart.confidential_hart().is_dummy());
        Self { hardware_hart }
    }

    #[no_mangle]
    extern "C" fn route_non_confidential_flow(hart_ptr: *mut HardwareHart) -> ! {
        let hardware_hart = unsafe { hart_ptr.as_mut().expect(crate::error::CTX_SWITCH_ERROR_MSG) };
        let mut flow = Self::create(hardware_hart);
        flow.hypervisor_hart_mut().csrs_mut().mepc.save();
        flow.hypervisor_hart_mut().csrs_mut().mstatus.save();

        match TrapCause::from_hart_architectural_state(flow.hypervisor_hart().hypervisor_hart_state()) {
            Interrupt => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            IllegalInstruction => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAddressMisaligned => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAccessFault => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAddressMisaligned => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAccessFault => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Ace(ResumeConfidentialHart)) => ResumeRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Ace(TerminateConfidentialVm)) => TerminateRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(_) => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            VsEcall(Ace(PromoteToConfidentialVm)) => PromoteToConfidentialVm::from_vm_hart(flow.hypervisor_hart()).handle(flow),
            VsEcall(_) => SbiVmRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            MachineEcall => OpensbiRequest::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    pub fn into_confidential_flow(self, request: ResumeRequest) -> (NonConfidentialFlow<'a>, Error) {
        match ControlData::try_confidential_vm(request.confidential_vm_id(), |mut confidential_vm| {
            confidential_vm.steal_confidential_hart(request.confidential_hart_id(), self.hardware_hart)
        }) {
            Ok(_) => ConfidentialFlow::resume_confidential_hart_execution(self.hardware_hart),
            Err(error) => (self, error),
        }
    }

    pub fn exit_to_hypervisor(mut self, transformation: ExposeToHypervisor) -> ! {
        match transformation {
            ExposeToHypervisor::SbiRequest(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::SbiResult(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::SbiVmRequest(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::OpensbiResult(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::Resume() => {}
        }
        // Loads control and status registers (CSRs) that might have changed during execution of the security monitor. This function
        // should be called just before exiting to the assembly context switch, so when we are sure that these CSRs have their
        // final values.
        self.hypervisor_hart().csrs().mepc.restore();
        self.hypervisor_hart().csrs().mstatus.restore();
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Swaps the mscratch register value with the original mascratch value used by OpenSBI. This function must be
    /// called before executing any OpenSBI function. We can remove this once we get rid of the OpenSBI firmware.
    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }

    pub fn restore_original_gprs(&mut self) {
        use crate::core::architecture::GeneralPurposeRegister;
        // Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GRPs).
        // GRPs might carry SBI- or MMIO-related reponses, so using GRPs would destroy the communication between the
        // hypervisor and confidential VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V
        // NACL extension that solves these problems by using shared memory region in which the SBI- and MMIO-related
        // information is transfered. Below we restore the original `a7` and `a6`.
        let original_a7 = self.hypervisor_hart_mut().csrs_mut().vstval.read();
        let original_a6 = self.hypervisor_hart_mut().csrs_mut().vsepc.read();
        self.hypervisor_hart_mut().gprs_mut().write(GeneralPurposeRegister::a7, original_a7);
        self.hypervisor_hart_mut().gprs_mut().write(GeneralPurposeRegister::a6, original_a6);
    }

    fn hypervisor_hart_mut(&mut self) -> &mut HypervisorHart {
        self.hardware_hart.hypervisor_hart_mut()
    }

    fn hypervisor_hart(&self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }
}
