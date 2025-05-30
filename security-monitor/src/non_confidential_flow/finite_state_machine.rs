// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::riscv::sbi::BaseExtension::*;
use crate::core::architecture::riscv::sbi::CovhExtension::*;
use crate::core::architecture::riscv::sbi::NaclExtension::*;
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::riscv::sbi::SbiExtension::*;
use crate::core::architecture::specification::CAUSE_SUPERVISOR_ECALL;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{TrapCause, CSR};
use crate::core::control_data::{ConfidentialVmId, HardwareHart, HypervisorHart};
use crate::error::Error;
use crate::non_confidential_flow::handlers::cove_host_extension::{
    DestroyConfidentialVm, GetSecurityMonitorInfo, PromoteToConfidentialVm, RunConfidentialHart,
};
use crate::non_confidential_flow::handlers::nested_acceleration_extension::{NaclProbeFeature, NaclSetupSharedMemory};
use crate::non_confidential_flow::handlers::supervisor_binary_interface::{InvalidCall, ProbeSbiExtension};
use crate::non_confidential_flow::{ApplyToHypervisorHart, DeclassifyToHypervisor};
use opensbi_sys::sbi_trap_regs;

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
        let hardware_hart = unsafe { &mut *hart_ptr };
        // Performance optimziation: we do not want to add overhead when delegating calls to OpenSBI, thus make sure we do not
        // create extra objects on heap or make unnecessary load/stores.
        if CSR.mcause.read() != CAUSE_SUPERVISOR_ECALL.into() {
            hardware_hart.call_opensbi_trap_handler();
            unsafe { exit_to_hypervisor_asm() };
        }

        let mut flow = Self::create(hardware_hart);
        match TrapCause::from_hart_architectural_state(flow.hypervisor_hart().hypervisor_hart_state()) {
            HsEcall(Base(ProbeExtension)) => ProbeSbiExtension::from_hypervisor_hart(flow.hypervisor_hart_mut()).handle(flow),
            HsEcall(Covh(TsmGetInfo)) => GetSecurityMonitorInfo::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(PromoteToTvm)) => PromoteToConfidentialVm::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(TvmVcpuRun)) => RunConfidentialHart::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(DestroyTvm)) => DestroyConfidentialVm::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(_)) => InvalidCall::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(ProbeFeature)) => NaclProbeFeature::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(SetupSharedMemory)) => NaclSetupSharedMemory::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(_)) => InvalidCall::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            _ => flow.delegate_to_opensbi(),
        }
    }

    pub fn delegate_to_opensbi(self) -> ! {
        self.hardware_hart.call_opensbi_trap_handler();
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Tries to traverse to confidential flow of the finite state machine (FSM). Returns error if the identifier of a confidential VM or
    /// hart are incorrect or cannot be scheduled for execution.
    pub fn into_confidential_flow(
        self, confidential_vm_id: ConfidentialVmId, confidential_hart_id: usize,
    ) -> Result<(usize, ConfidentialFlow<'a>), (NonConfidentialFlow<'a>, Error)> {
        ConfidentialFlow::enter_from_non_confidential_flow(self.hardware_hart, confidential_vm_id, confidential_hart_id)
            .map_err(|(hardware_hart, error)| (Self::create(hardware_hart), error))
    }

    pub fn declassify_to_hypervisor_hart(mut self, declassify: DeclassifyToHypervisor) -> Self {
        match declassify {
            DeclassifyToHypervisor::SbiRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::SbiResponse(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::Interrupt(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::MmioLoadRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::MmioStoreRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            DeclassifyToHypervisor::EnabledInterrupts(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
        }
        self
    }

    /// Resumes execution of the hypervisor hart and declassifies information from a confidential VM to the hypervisor. This is an exit node
    /// (Rust->Assembly) of the non-confidential part of the finite state machine (FSM), executed as a result of confidential VM
    /// execution (there was context switch between security domains).
    pub fn declassify_and_exit_to_hypervisor(self, declassify: DeclassifyToHypervisor) -> ! {
        self.declassify_to_hypervisor_hart(declassify);
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Resumes execution of the hypervisor hart and applies state transformation. This is an exit node (Rust->Assembly) of the
    /// non-confidential part of the finite state machine (FSM), executed as a result of processing hypervisor request (there was no
    /// context switch between security domains).
    pub(super) fn apply_and_exit_to_hypervisor(mut self, transformation: ApplyToHypervisorHart) -> ! {
        match transformation {
            ApplyToHypervisorHart::SbiResponse(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisorHart::SetSharedMemory(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisorHart::PromoteResponse((v, r)) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut(), r),
        }
        unsafe { exit_to_hypervisor_asm() }
    }

    pub fn shared_memory(&self) -> &NaclSharedMemory {
        self.hypervisor_hart().shared_memory()
    }

    fn hypervisor_hart_mut(&mut self) -> &mut HypervisorHart {
        self.hardware_hart.hypervisor_hart_mut()
    }

    fn hypervisor_hart(&self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }
}
