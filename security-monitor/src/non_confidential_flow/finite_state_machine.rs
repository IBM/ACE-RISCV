// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::riscv::sbi::BaseExtension::*;
use crate::core::architecture::riscv::sbi::CovhExtension::*;
use crate::core::architecture::riscv::sbi::NaclExtension::*;
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::riscv::sbi::SbiExtension::*;
use crate::core::architecture::TrapCause::*;
use crate::core::architecture::{GeneralPurposeRegister, TrapCause};
use crate::core::control_data::{ConfidentialVmId, HardwareHart, HypervisorHart};
use crate::error::Error;
use crate::non_confidential_flow::handlers::cove_host_extension::{
    DestroyConfidentialVm, GetSecurityMonitorInfo, PromoteToConfidentialVm, RunConfidentialHart,
};
use crate::non_confidential_flow::handlers::nested_acceleration_extension::{NaclProbeFeature, NaclSetupSharedMemory};
use crate::non_confidential_flow::handlers::opensbi::{DelegateToOpensbi, ProbeSbiExtension};
use crate::non_confidential_flow::handlers::supervisor_binary_interface::InvalidCall;
use crate::non_confidential_flow::{ApplyToHypervisorHart, DeclassifyToHypervisor};

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
    const CTX_SWITCH_ERROR_MSG: &'static str = "Bug: invalid argument provided by the assembly context switch";

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
        let tt = TrapCause::from_hart_architectural_state(flow.hypervisor_hart().hypervisor_hart_state());
        use crate::core::architecture::sbi::CovhExtension;
        use crate::core::architecture::CSR;
        match tt {
            Interrupt => {}
            IllegalInstruction => {}
            LoadAddressMisaligned => {}
            LoadAccessFault => {}
            StoreAddressMisaligned => {}
            StoreAccessFault => {}
            HsEcall(_) => {
                let a7 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a7);
                let a6 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a6);
                if a7 != 0x54494D45 {
                    debug!(
                        "Enter SM non-conf flow due to {:?} {:x} {:x} mepc={:x} mscratch={:x} openbsi={:x}",
                        tt,
                        a7,
                        a6,
                        flow.hypervisor_hart().csrs().mepc.read_from_main_memory(),
                        CSR.mhartid.read(),
                        flow.hardware_hart.previous_mscratch,
                    );
                }
            }
            MachineEcall => {
                let a7 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a7);
                let a6 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a6);
                if a7 != 0x54494D45 {
                    debug!(
                        "Enter SM non-conf flow due to {:?} {:x} {:x} mepc={:x} mscratch={:x} openbsi={:x}",
                        tt,
                        a7,
                        a6,
                        flow.hypervisor_hart().csrs().mepc.read_from_main_memory(),
                        CSR.mhartid.read(),
                        flow.hardware_hart.previous_mscratch,
                    );
                }
            }
            FetchPageFault => {}
            LoadPageFault => {}
            StorePageFault => {}
            _ => {
                let a7 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a7);
                let a6 = flow.hypervisor_hart().gprs().read(GeneralPurposeRegister::a6);
                if a7 != 0x54494D45 {
                    debug!(
                        "Enter SM non-conf flow due to {:?} {:x} {:x} mepc={:x} mscratch={:x} openbsi={:x}",
                        tt,
                        a7,
                        a6,
                        flow.hypervisor_hart().csrs().mepc.read_from_main_memory(),
                        CSR.mhartid.read(),
                        flow.hardware_hart.previous_mscratch,
                    );
                }
            }
        }
        match tt {
            Interrupt => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            IllegalInstruction => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAddressMisaligned => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadAccessFault => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAddressMisaligned => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StoreAccessFault => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Base(ProbeExtension)) => ProbeSbiExtension::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(TsmGetInfo)) => GetSecurityMonitorInfo::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(PromoteToTvm)) => PromoteToConfidentialVm::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(TvmVcpuRun)) => RunConfidentialHart::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(DestroyTvm)) => DestroyConfidentialVm::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Covh(_)) => InvalidCall::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(ProbeFeature)) => NaclProbeFeature::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(SetupSharedMemory)) => NaclSetupSharedMemory::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(Nacl(_)) => InvalidCall::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            HsEcall(_) => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            MachineEcall => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            FetchPageFault => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            LoadPageFault => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            StorePageFault => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            _ => DelegateToOpensbi::from_hypervisor_hart(flow.hypervisor_hart()).handle(flow),
            // trap_reason => {
            //     crate::debug::__print_hart_state(flow.hypervisor_hart().hypervisor_hart_state());
            //     panic!(
            //         "Non-confidential trap handler in hart {}: Unsupported exception {:?}",
            //         flow.hardware_hart.confidential_hart().confidential_hart_id(),
            //         trap_reason
            //     );
            // }
        }
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
            ApplyToHypervisorHart::OpenSbiResponse(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ApplyToHypervisorHart::SetSharedMemory(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
        }
        unsafe { exit_to_hypervisor_asm() }
    }

    /// Swaps the mscratch register value with the original mascratch value used by OpenSBI. This function must be
    /// called before executing any OpenSBI function. We can remove this once we get rid of the OpenSBI firmware.
    pub fn swap_mscratch(&mut self) {
        self.hardware_hart.swap_mscratch()
    }

    pub fn shared_memory(&self) -> &NaclSharedMemory {
        self.hypervisor_hart().shared_memory()
    }

    fn hypervisor_hart_mut(&mut self) -> &mut HypervisorHart {
        self.hardware_hart.hypervisor_hart_mut()
    }

    pub fn hypervisor_hart(&self) -> &HypervisorHart {
        &self.hardware_hart.hypervisor_hart()
    }
}
