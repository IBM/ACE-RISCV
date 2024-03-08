// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{
    disable_bit, is_bit_enabled, FloatingPointRegisters, GeneralPurposeRegister, GeneralPurposeRegisters, HartArchitecturalState,
    HartLifecycleState, TrapCause, CSR, CSR_MSTATUS_MPRV, CSR_STATUS_SIE, ECALL_INSTRUCTION_LENGTH,
};
use crate::core::control_data::ConfidentialVmId;
use crate::core::transformations::{
    EnabledInterrupts, ExposeToConfidentialVm, GuestLoadPageFaultRequest, GuestLoadPageFaultResult, GuestStorePageFaultRequest,
    GuestStorePageFaultResult, InjectedInterrupts, InterHartRequest, InterruptRequest, MmioLoadRequest, MmioStoreRequest, PendingRequest,
    SbiHsmHartStart, SbiHsmHartStatus, SbiHsmHartSuspend, SbiIpi, SbiRemoteFenceI, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid, SbiRequest,
    SbiResult, SharePageRequest, UnsharePageRequest, VirtualInstructionRequest, VirtualInstructionResult,
};
use crate::error::Error;

extern "C" {
    // Assembly function that is an entry point to the security monitor from the hypervisor or a virtual machine.
    fn enter_from_confidential_hart_asm();
}

/// ConfidentialHart represents the dump state of the confidential VM's hart (aka vcpu). The only publicly exposed way
/// to modify the confidential hart architectural state (registers/CSRs) is by calling the constructor or applying a
/// transformation.
#[repr(C)]
pub struct ConfidentialHart {
    // Safety: HardwareHart and ConfidentialHart must both start with the HartArchitecturalState element
    // because based on this we automatically calculate offsets of registers' and CSRs' for the asm code.
    confidential_hart_state: HartArchitecturalState,
    // If there is no confidential vm id assigned to this hart then it means that this confidential hart is a dummy
    // one. A dummy virtual hart means that the confidential_hart is not associated with any confidential VM but is
    // used to prevent some concurrency issues like attempts of assigning the same confidential hart to many physical
    // cores.
    confidential_vm_id: Option<ConfidentialVmId>,
    /// The confidential hart's lifecycle follow the finite state machine (FSM) of a hart defined in SBI HSM extension.
    lifecycle_state: HartLifecycleState,
    /// A pending request indicates that the confidential hart sent a request to the hypervisor and is waiting for its
    /// reply. The pending request defines the expected response.
    pending_request: Option<PendingRequest>,
}

impl ConfidentialHart {
    /// Constructs a dummy hart. This dummy hart carries no confidential information. It is used to indicate that a real
    /// confidential hart has been assigned to a hardware hart for execution.
    pub fn dummy(id: usize) -> Self {
        // The lifecycle state of the dummy hart is Started because it means that the confidential hart is assigned for execution and this
        // is only possible when the confidential hart is in the Started state.
        Self::new(HartArchitecturalState::empty(id), HartLifecycleState::Started)
    }

    /// Constructs a confidential hart with the state after a reset.
    pub fn from_vm_hart_reset(id: usize, from: &HartArchitecturalState) -> Self {
        let mut confidential_hart_state = HartArchitecturalState::from_existing(id, from);
        GeneralPurposeRegisters::iter().for_each(|x| {
            confidential_hart_state.gprs.0[x] = 0;
        });
        FloatingPointRegisters::iter().for_each(|x| {
            confidential_hart_state.fprs.0[x] = 0;
        });
        // TODO: reset PC and other state-related csrs
        Self::new(confidential_hart_state, HartLifecycleState::Stopped)
    }

    pub fn from_vm_hart(id: usize, from: &HartArchitecturalState) -> Self {
        let hart_architectural_state = HartArchitecturalState::from_existing(id, from);
        let mut confidential_hart = Self::new(hart_architectural_state, HartLifecycleState::Started);
        // We create a virtual hart as a result of the SBI request the ESM call traps in the security monitor, which
        // creates the confidential VM but then the security monitor makes an SBI call to the hypervisor to let him know
        // that this VM become an confidential VM. The hypervisor should then return to the confidential VM providing it
        // with the result of this transformation.
        confidential_hart.pending_request = Some(PendingRequest::SbiRequest());
        confidential_hart
    }

    fn new(mut confidential_hart_state: HartArchitecturalState, lifecycle_state: HartLifecycleState) -> Self {
        use crate::core::architecture::{MIE_STIP_MASK, MIE_VSEIP_MASK, MIE_VSSIP_MASK, MIE_VSTIP_MASK};
        let confidential_vm_id = None;
        let pending_request = None;
        // delegate VS-level interrupts directly to the confidential VM. All other
        // interrupts will trap in the security monitor.
        confidential_hart_state.mideleg = MIE_VSSIP_MASK | MIE_VSTIP_MASK | MIE_VSEIP_MASK;
        confidential_hart_state.hideleg = confidential_hart_state.mideleg;
        // vsie reflects hie, we allow only VS interrupts
        confidential_hart_state.hie = confidential_hart_state.mideleg;
        // Allow only hypervisor's timer interrupts to preemt confidential VM's execution
        confidential_hart_state.mie = MIE_STIP_MASK;

        // delegate exceptions that can be handled directly in the confidential VM
        confidential_hart_state.medeleg = 0b000000001011000111111111;
        confidential_hart_state.hedeleg = confidential_hart_state.medeleg;

        confidential_hart_state.mtvec = enter_from_confidential_hart_asm as usize;

        Self { confidential_vm_id, confidential_hart_state, lifecycle_state, pending_request }
    }

    pub fn set_confidential_vm_id(&mut self, confidential_vm_id: ConfidentialVmId) {
        self.confidential_vm_id = Some(confidential_vm_id);
    }

    pub fn confidential_vm_id(&self) -> Option<ConfidentialVmId> {
        self.confidential_vm_id
    }

    pub fn confidential_hart_id(&self) -> usize {
        self.confidential_hart_state.id
    }

    pub fn take_request(&mut self) -> Option<PendingRequest> {
        self.pending_request.take()
    }

    pub fn is_dummy(&self) -> bool {
        self.confidential_vm_id.is_none()
    }

    /// Returns true if this confidential hart can be scheduled on the physical hart.
    pub fn is_executable(&self) -> bool {
        let hart_states_allowed_to_resume = [HartLifecycleState::Started, HartLifecycleState::StartPending, HartLifecycleState::Suspended];
        !self.is_dummy() && hart_states_allowed_to_resume.contains(&self.lifecycle_state)
    }

    /// Stores a pending request inside the confidential hart's state. Before the next execution of this confidential
    /// hart, the security monitor will declassify a response to this request that should come from another security
    /// domain, like hypervisor.
    pub fn set_pending_request(&mut self, request: PendingRequest) -> Result<(), Error> {
        assure!(self.pending_request.is_none(), Error::PendingRequest())?;
        self.pending_request = Some(request);
        Ok(())
    }

    pub fn store_confidential_hart_state_in_main_memory(&mut self) -> EnabledInterrupts {
        self.confidential_hart_state.store_processor_state_in_main_memory();
        self.enabled_interrupts()
    }

    pub fn load_confidential_hart_state_from_main_memory(&mut self, interrupts_to_inject: InjectedInterrupts) {
        self.confidential_hart_state.load_processor_state_from_main_memory();
        self.apply_injected_interrupts(interrupts_to_inject);
    }
}

// Methods related to lifecycle state transitions of the confidential hart. These methods manipulate the internal hart
// state in a response to requests from (1) the confidential hart itself (started->stop or started->suspend), from
// other confidential hart (stopped->started), or hypervisor (suspend->started). Check out the SBI' HSM extensions for
// more details.
impl ConfidentialHart {
    pub fn lifecycle_state(&self) -> &HartLifecycleState {
        &self.lifecycle_state
    }

    /// Changes the lifecycle state of the hart into the `StartPending` state. Confidential hart's state is set as if
    /// the hart was reset. This function is called as a response of another confidential hart (typically a boot hart)
    /// to start another confidential hart. Returns error if the confidential hart is not in stopped state.
    pub fn transition_from_stopped_to_start_pending(&mut self, request: SbiHsmHartStart) -> Result<(), Error> {
        // A hypervisor might try to schedule a stopped confidential hart. This is forbidden.
        assure!(self.lifecycle_state == HartLifecycleState::Stopped, Error::CannotStartNotStoppedHart())?;
        // if this is a dummy hart, then the confidential hart is already running, i.e., it is in the `started` state.
        assure_not!(self.is_dummy(), Error::HartAlreadyRunning())?;
        // let's set up the confidential hart so that it can be run
        self.lifecycle_state = HartLifecycleState::StartPending;
        self.pending_request = Some(PendingRequest::SbiHsmHartStartPending());
        // Following the SBI documentation of the function `hart start` in the HSM extension, only satp, sstatus.SIE,
        // a0, a1 have defined values, all other registers are in an undefined state. The hart will start
        // executing in the supervisor mode.
        // We clear all VS-related state but leave the configuration of M/HS-mode related registers, for example, we
        // want the interrupt delegations configuration to remain untouched.
        self.confidential_hart_state.reset();
        self.confidential_hart_state.vsatp = 0;
        disable_bit(&mut self.confidential_hart_state.sstatus, CSR_STATUS_SIE);
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a1, self.confidential_hart_id());
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a2, request.opaque);
        self.confidential_hart_state.mepc = request.start_address;
        Ok(())
    }

    /// Changes the lifecycle state of the confidential hart to the `Started` state.
    pub fn transition_from_start_pending_to_started(&mut self) {
        assert!(!self.is_dummy());
        if self.lifecycle_state == HartLifecycleState::StartPending {
            self.lifecycle_state = HartLifecycleState::Started;
        }
    }

    pub fn transition_from_started_to_suspended(&mut self, _request: SbiHsmHartSuspend) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotSuspedNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Suspended;
        Ok(())
    }

    pub fn transition_from_started_to_stopped(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Started, Error::CannotStopNotStartedHart())?;
        self.lifecycle_state = HartLifecycleState::Stopped;
        Ok(())
    }

    pub fn transition_from_suspended_to_started(&mut self) -> Result<(), Error> {
        assert!(!self.is_dummy());
        assure!(self.lifecycle_state == HartLifecycleState::Suspended, Error::CannotStartNotSuspendedHart())?;
        self.lifecycle_state = HartLifecycleState::Started;
        Ok(())
    }

    pub fn transition_to_shutdown(&mut self) {
        assert!(!self.is_dummy());
        self.lifecycle_state = HartLifecycleState::Shutdown;
    }
}

// Methods that declassify information from the hypervisor and expose them to the confidential hart.
impl ConfidentialHart {
    pub fn apply(&mut self, transformation: ExposeToConfidentialVm) -> usize {
        match transformation {
            ExposeToConfidentialVm::SbiResult(v) => self.apply_sbi_result(v),
            ExposeToConfidentialVm::GuestLoadPageFaultResult(v) => self.apply_guest_load_page_fault_result(v),
            ExposeToConfidentialVm::VirtualInstructionResult(v) => self.apply_virtual_instruction_result(v),
            ExposeToConfidentialVm::GuestStorePageFaultResult(v) => self.apply_guest_store_page_fault_result(v),
            ExposeToConfidentialVm::SbiIpi(v) => self.apply_sbi_ipi(v),
            ExposeToConfidentialVm::SbiRemoteFenceI(v) => self.apply_sbi_remote_fence_i(v),
            ExposeToConfidentialVm::SbiRemoteSfenceVma(v) => self.apply_sbi_remote_sfence_vma(v),
            ExposeToConfidentialVm::SbiRemoteSfenceVmaAsid(v) => self.apply_sbi_remote_sfence_vma_asid(v),
            ExposeToConfidentialVm::SbiHsmHartStartPending() => self.transition_from_start_pending_to_started(),
            ExposeToConfidentialVm::SbiHsmHartStart() => self.apply_sbi_result_success(),
            ExposeToConfidentialVm::SbiSrstSystemReset() => self.transition_to_shutdown(),
            ExposeToConfidentialVm::Resume() => {}
        }
        core::ptr::addr_of!(self.confidential_hart_state) as usize
    }

    fn apply_injected_interrupts(&mut self, result: InjectedInterrupts) {
        CSR.hvip.set(result.hvip | self.confidential_hart_state.vsip);
    }

    fn apply_interrupt(&mut self, result: InterruptRequest) {
        // Interrupts are exposed to the virtual machine via the HVIP register
        // We assume here that the input code reflects the correct interrupt code intended for the virtual machine.
        CSR.hvip.read_and_set_bits(result.mask());
    }

    fn apply_sbi_ipi(&mut self, _result: SbiIpi) {
        use crate::core::architecture::MIE_VSSIP;
        // IPI exposes itself as supervisor-level software interrupt this is the 2nd bit of the vsip controlled by the
        // hvip register. Check the RISC-V privileged specification for more information.
        self.apply_interrupt(InterruptRequest::new(MIE_VSSIP))
    }

    fn apply_sbi_remote_fence_i(&mut self, _result: SbiRemoteFenceI) {
        crate::core::architecture::fence_i();
    }

    fn apply_sbi_remote_sfence_vma(&mut self, _result: SbiRemoteSfenceVma) {
        // TODO: execute a more fine grained fence. Right now, we just do the full TLB flush
        crate::core::architecture::sfence_vma();
    }

    fn apply_sbi_remote_sfence_vma_asid(&mut self, _result: SbiRemoteSfenceVmaAsid) {
        // TODO: execute a more fine grained fence. Right now, we just do the full TLB flush
        crate::core::architecture::sfence_vma();
    }

    fn apply_sbi_result(&mut self, result: SbiResult) {
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a0, result.a0());
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a1, result.a1());
        self.confidential_hart_state.mepc += result.pc_offset();
    }

    fn apply_sbi_result_success(&mut self) {
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a0, 0);
        self.confidential_hart_state.set_gpr(GeneralPurposeRegister::a1, 0);
        self.confidential_hart_state.mepc += ECALL_INSTRUCTION_LENGTH;
    }

    fn apply_guest_load_page_fault_result(&mut self, result: GuestLoadPageFaultResult) {
        self.confidential_hart_state.set_gpr(result.result_gpr(), result.value());
        self.confidential_hart_state.mepc += result.instruction_length();
    }

    fn apply_guest_store_page_fault_result(&mut self, result: GuestStorePageFaultResult) {
        self.confidential_hart_state.mepc += result.instruction_length();
    }

    fn apply_virtual_instruction_result(&mut self, result: VirtualInstructionResult) {
        self.confidential_hart_state.mepc += result.instruction_length();
    }
}

// Methods to declassify portions of confidential hart state.
impl ConfidentialHart {
    pub fn trap_reason(&self) -> TrapCause {
        let cause = CSR.mcause.read();
        let extension_id = self.confidential_hart_state.gpr(GeneralPurposeRegister::a7);
        let function_id = self.confidential_hart_state.gpr(GeneralPurposeRegister::a6);
        TrapCause::from(cause, extension_id, function_id)
    }

    pub fn hypercall_request(&self) -> SbiRequest {
        SbiRequest::from_hart_state(&self.confidential_hart_state)
    }

    pub fn virtual_instruction_request(&self) -> VirtualInstructionRequest {
        let (instruction, instruction_length) = self.read_faulted_instruction();
        VirtualInstructionRequest { instruction, instruction_length }
    }

    pub fn guest_load_page_fault_request(&self) -> Result<(GuestLoadPageFaultRequest, MmioLoadRequest), Error> {
        let mcause = CSR.mcause.read();
        let (instruction, instruction_length) = self.read_faulted_instruction();
        let gpr = crate::core::architecture::decode_result_register(instruction)?;
        let mtval = CSR.mtval.read();
        let mtval2 = CSR.mtval2.read();

        let load_fault_request = GuestLoadPageFaultRequest::new(instruction_length, gpr);
        let mmio_load_request = MmioLoadRequest::new(mcause, mtval, mtval2, instruction);

        Ok((load_fault_request, mmio_load_request))
    }

    pub fn guest_store_page_fault_request(&self) -> Result<(GuestStorePageFaultRequest, MmioStoreRequest), Error> {
        let mcause = CSR.mcause.read();
        let (instruction, instruction_length) = self.read_faulted_instruction();
        let gpr = crate::core::architecture::decode_result_register(instruction)?;
        let gpr_value = self.confidential_hart_state.gpr(gpr);
        let mtval = CSR.mtval.read();
        let mtval2 = CSR.mtval2.read();

        let guest_store_page_fault_request = GuestStorePageFaultRequest::new(instruction_length);
        let mmio_store_request = MmioStoreRequest::new(mcause, mtval, mtval2, instruction, gpr, gpr_value);

        Ok((guest_store_page_fault_request, mmio_store_request))
    }

    pub fn share_page_request(&self) -> Result<(SharePageRequest, SbiRequest), Error> {
        let shared_page_address = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let share_page_request = SharePageRequest::new(shared_page_address)?;
        let sbi_request = SbiRequest::kvm_ace_page_in(shared_page_address);
        Ok((share_page_request, sbi_request))
    }

    pub fn unshare_page_request(&self) -> Result<UnsharePageRequest, Error> {
        let page_to_unshare_address = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        Ok(UnsharePageRequest::new(page_to_unshare_address)?)
    }

    pub fn sbi_ipi(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        InterHartRequest::SbiIpi(SbiIpi::new(hart_mask, hart_mask_base))
    }

    pub fn sbi_hsm_hart_start(&self) -> SbiHsmHartStart {
        let confidential_hart_id = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let boot_code_address = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        let blob = self.confidential_hart_state.gpr(GeneralPurposeRegister::a2);
        SbiHsmHartStart::new(confidential_hart_id, boot_code_address, blob)
    }

    pub fn sbi_hsm_hart_suspend(&self) -> SbiHsmHartSuspend {
        let suspend_type = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let resume_addr = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        let opaque = self.confidential_hart_state.gpr(GeneralPurposeRegister::a2);
        SbiHsmHartSuspend::new(suspend_type, resume_addr, opaque)
    }

    pub fn sbi_hsm_hart_status(&self) -> SbiHsmHartStatus {
        let confidential_hart_id = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        SbiHsmHartStatus::new(confidential_hart_id)
    }

    pub fn sbi_remote_fence_i(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        InterHartRequest::SbiRemoteFenceI(SbiRemoteFenceI::new(hart_mask, hart_mask_base))
    }

    pub fn sbi_remote_sfence_vma(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        let start_address = self.confidential_hart_state.gpr(GeneralPurposeRegister::a2);
        let size = self.confidential_hart_state.gpr(GeneralPurposeRegister::a3);
        InterHartRequest::SbiRemoteSfenceVma(SbiRemoteSfenceVma::new(hart_mask, hart_mask_base, start_address, size))
    }

    pub fn sbi_remote_sfence_vma_asid(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GeneralPurposeRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GeneralPurposeRegister::a1);
        let start_address = self.confidential_hart_state.gpr(GeneralPurposeRegister::a2);
        let size = self.confidential_hart_state.gpr(GeneralPurposeRegister::a3);
        let asid = self.confidential_hart_state.gpr(GeneralPurposeRegister::a4);
        InterHartRequest::SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid::new(hart_mask, hart_mask_base, start_address, size, asid))
    }

    pub fn enabled_interrupts(&self) -> EnabledInterrupts {
        EnabledInterrupts::new()
    }

    fn read_faulted_instruction(&self) -> (usize, usize) {
        // mepc stores the virtual address of the instruction that caused trap. Setting
        // mstatus.MPRV bit allows reading the faulting instruction in memory using the
        // virtual address.
        let fault_instruction_virtual_address = self.confidential_hart_state.mepc as *const usize;
        let is_mprv_set = is_bit_enabled(CSR.mstatus.read(), CSR_MSTATUS_MPRV);
        CSR.mstatus.read_and_set_bit(CSR_MSTATUS_MPRV);
        let instruction = unsafe {
            let instruction = fault_instruction_virtual_address.read_volatile();
            instruction
        };
        if !is_mprv_set {
            CSR.mstatus.read_and_clear_bit(CSR_MSTATUS_MPRV);
        }

        // We only expose the faulting instruction, which can be of different length.
        // Therefore, we must trim the read memory to this size by disabling unwanted
        // bits after learning what is the size of the fault instruction.
        let instruction_length = riscv_decode::instruction_length(instruction as u16);
        let mask = (1 << 8 * instruction_length) - 1;
        let instruction = (instruction & mask) as usize;

        (instruction, instruction_length)
    }
}
