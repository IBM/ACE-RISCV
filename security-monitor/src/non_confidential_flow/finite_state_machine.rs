// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::{ConfidentialFlow, DeclassifyToHypervisor};
use crate::core::architecture::AceExtension::*;
use crate::core::architecture::SbiExtension::*;
use crate::core::architecture::TrapCause;
use crate::core::architecture::TrapCause::*;
use crate::core::control_data::{ConfidentialVmId, HardwareHart, HypervisorHart};
use crate::error::Error;
use crate::non_confidential_flow::handlers::delegate_hypercall::SbiVmHandler;
use crate::non_confidential_flow::handlers::delegate_to_opensbi::OpensbiHandler;
use crate::non_confidential_flow::handlers::promote_vm::PromoteVmHandler;
use crate::non_confidential_flow::handlers::resume_confidential_hart::ResumeHandler;
use crate::non_confidential_flow::handlers::terminate_confidential_vm::TerminateVmHandler;
use crate::non_confidential_flow::ApplyToHypervisor;

extern "C" {
    /// To ensure safety, specify all possible valid states that KVM expects to see and prove that security monitor
    /// never returns to KVM with other state. For example, only a subset of exceptions/interrupts can be handled by KVM.
    /// KVM kill the vcpu if it receives unexpected exception because it does not know what to do with it.
    fn exit_to_hypervisor_asm() -> !;
}

/// Represents the non-confidential part of the finite state machine (FSM), implementing router and exit nodes. It encapsulates the
/// HardwareHart instance, which is never exposed. It invokes handlers providing them temporary read access to hypervisor hart state.
pub struct NonConfidentialFlow<'a> {
    hardware_hart: &'a mut HardwareHart,
}

impl<'a> NonConfidentialFlow<'a> {
    pub const CTX_SWITCH_ERROR_MSG: &'static str = "Bug: invalid argument provided by the assembly context switch";

    /// Creates an instance of the `NonConfidentialFlow`. A confidential hart must not be assigned to the hardware hart.
    pub fn create(hardware_hart: &'a mut HardwareHart) -> Self {
        assert!(hardware_hart.confidential_hart().is_dummy());
        Self { hardware_hart }
    }

    /// Routes control flow execution based on the trap cause. This is an entry node (Assembly->Rust) of the non-confidential flow part of
    /// the finite state machine (FSM).
    ///
    /// # Safety
    ///
    /// * A confidential hart must not be assigned to the hardware hart.
    /// * This function must only be invoked by the assembly lightweight context switch.
    /// * Pointer is a not null and points to a memory region owned by the physical hart executing this code.
    #[no_mangle]
    unsafe extern "C" fn route_trap_from_hypervisor_or_vm(hart_ptr: *mut HardwareHart) -> ! {
        // Below unsafe is ok because the lightweight context switch (assembly) guarantees that it provides us with a valid pointer to the
        // hardware hart's dump area in main memory. This area in main memory is exclusively owned by the physical hart executing this code.
        // Specifically, every physical hart has its own are in the main memory and its `mscratch` register stores the address. See the
        // `initialization` procedure for more details.
        let flow = unsafe { Self::create(hart_ptr.as_mut().expect(Self::CTX_SWITCH_ERROR_MSG)) };
        match TrapCause::from_hart_architectural_state(flow.hypervisor_hart().hypervisor_hart_state()) {
            Interrupt => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            IllegalInstruction => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAddressMisaligned => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAccessFault => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAddressMisaligned => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAccessFault => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Ace(ResumeConfidentialHart)) => ResumeHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Ace(TerminateConfidentialVm)) => TerminateVmHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(_) => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            VsEcall(Ace(PromoteVmHandler)) => PromoteVmHandler::from_vm_hart(flow.hypervisor_hart()).handle(flow),
            VsEcall(_) => SbiVmHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            MachineEcall => OpensbiHandler::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            trap_reason => panic!("Bug: Incorrect interrupt delegation configuration: {:?}", trap_reason),
        }
    }

    /// Tries to traverse to confidential flow of the finite state machine (FSM). Returns error if the identifier of a confidential VM or
    /// hart are incorrect or cannot be scheduled for execution.
    pub fn into_confidential_flow(
        self, confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize,
    ) -> Result<ConfidentialFlow<'a>, (NonConfidentialFlow<'a>, Error)> {
        ConfidentialFlow::enter_from_non_confidential_flow(self.hardware_hart, confidential_vm_id, confidential_hart_id)
            .map_err(|(hardware_hart, error)| (Self::create(hardware_hart), error))
    }

    /// Resumes execution of the hypervisor hart and declassifies information from a confidential VM to the hypervisor. This is an exit node
    /// (Rust->Assembly) of the non-confidential part of the finite state machine (FSM), executed as a result of confidential VM
    /// execution (there was context switch between security domains).
    pub fn declassify_and_exit_to_hypervisor(mut self, declassify: DeclassifyToHypervisor) -> ! {
        match declassify {
            DeclassifyToHypervisor::SbiRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::SbiResponse(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::Interrupt(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::MmioLoadRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::MmioStoreRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
        }
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Resumes execution of the hypervisor hart and applies state transformation. This is an exit node (Rust->Assembly) of the
    /// non-confidential part of the finite state machine (FSM), executed as a result of processing hypervisor request (there was no
    /// context switch between security domains).
    pub(super) fn apply_and_exit_to_hypervisor(mut self, transformation: ApplyToHypervisor) -> ! {
        match transformation {
            ApplyToHypervisor::SbiRequest(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisor::SbiResponse(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisor::SbiVmRequest(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisor::OpenSbiResponse(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
        }
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Swaps the mscratch register value with the original mascratch value used by OpenSBI. This function must be
    /// called before executing any OpenSBI function. We can remove this once we get rid of the OpenSBI firmware.
    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }

    /// Arguments to security monitor calls are stored in vs* CSRs because we cannot use regular general purpose registers (GPRs).
    /// GPRs might carry SBI- or MMIO-related reponses, so using GPRs would destroy the communication between the
    /// hypervisor and confidential VM. This is a hackish (temporal?) solution, we should probably move to the RISC-V
    /// NACL extension that solves these problems by using shared memory region in which the SBI- and MMIO-related
    /// information is transfered. Below we restore the original `a7` and `a6`.
    pub fn hack_restore_original_gprs(&mut self) {
        use crate::core::architecture::GeneralPurposeRegister;
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
