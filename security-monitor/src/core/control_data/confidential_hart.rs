// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{FpRegisters, GpRegister, GpRegisters, HartState, TrapReason};
use crate::core::control_data::ConfidentialVmId;
use crate::core::transformations::{
    ExposeToConfidentialVm, GuestLoadPageFaultRequest, GuestLoadPageFaultResult, GuestStorePageFaultRequest,
    GuestStorePageFaultResult, InterHartRequest, MmioLoadRequest, MmioStoreRequest, PendingRequest, SbiHsmHartStart,
    SbiIpi, SbiRemoteFenceI, SbiRemoteSfenceVma, SbiRemoteSfenceVmaAsid, SbiRequest, SbiResult, SharePageRequest,
};
use crate::error::Error;

/// ConfidentialHart represents the dump state of the confidential VM's hart (aka vcpu). The only publicly exposed way
/// to modify the virtual hart state (registers/CSRs) is by calling the constructor or applying a transformation.
#[repr(C)]
pub struct ConfidentialHart {
    // If there is no confidential vm id assigned to this hart then it means that this confidential hart is a dummy
    // one. A dummy virtual hart means that the confidential_hart is not associated with any confidential VM
    confidential_vm_id: Option<ConfidentialVmId>,
    // Safety: Careful, HardwareHart and ConfidentialHart must both start with the HartState element because based on
    // this we automatically calculate offsets of registers' and CSRs' for the asm code.
    confidential_hart_state: HartState,
    pending_request: Option<PendingRequest>,
}

impl ConfidentialHart {
    /// Constructs a dummy hart. This dummy hart carries no confidential information. It is used to indicate that a real
    /// confidential hart has been assigned to a hardware hart for execution.
    pub fn dummy(id: usize) -> Self {
        Self::new(HartState::empty(id))
    }

    /// Constructs a confidential hart with the state after a reset.
    pub fn from_vm_hart_reset(id: usize, from: &HartState) -> Self {
        let mut confidential_hart_state = HartState::from_existing(id, from);
        GpRegisters::iter().for_each(|x| {
            confidential_hart_state.gprs.0[x] = 0;
        });
        FpRegisters::iter().for_each(|x| {
            confidential_hart_state.fprs.0[x] = 0;
        });
        // TODO: reset PC and other state-related csrs
        Self::new(confidential_hart_state)
    }

    pub fn from_vm_hart(id: usize, from: &HartState) -> Self {
        let mut confidential_hart = Self::new(HartState::from_existing(id, from));
        // We create a virtual hart as a result of the SBI request the ESM call traps in the security monitor, which
        // creates the confidential VM but then the security monitor makes an SBI call to the hypervisor to let him know
        // that this VM become an confidential VM. The hypervisor should then return to the confidential VM providing it
        // with the result of this transformation.
        confidential_hart.pending_request = Some(PendingRequest::SbiRequest());
        confidential_hart
    }

    fn new(mut confidential_hart_state: HartState) -> Self {
        // delegate VS-level interrupts directly to the confidential VM. All other
        // interrupts will trap in the security monitor.
        confidential_hart_state.mideleg = 0b010001001110;
        confidential_hart_state.hideleg = confidential_hart_state.mideleg;

        // delegate exceptions that can be handled directly in the confidential VM
        confidential_hart_state.medeleg = 0b1011001111111111;
        confidential_hart_state.hedeleg = confidential_hart_state.medeleg;

        Self { confidential_hart_state, pending_request: None, confidential_vm_id: None }
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

    pub fn set_pending_request(&mut self, request: PendingRequest) -> Result<(), Error> {
        assure!(self.pending_request.is_none(), Error::PendingRequest())?;
        self.pending_request = Some(request);
        Ok(())
    }
}

// functions to inject information to a confidential VM.
impl ConfidentialHart {
    pub fn apply(&mut self, transformation: ExposeToConfidentialVm) -> usize {
        match transformation {
            ExposeToConfidentialVm::SbiResult(v) => self.apply_sbi_result(v),
            ExposeToConfidentialVm::GuestLoadPageFaultResult(v) => self.apply_guest_load_page_fault_result(v),
            ExposeToConfidentialVm::GuestStorePageFaultResult(v) => self.apply_guest_store_page_fault_result(v),
            ExposeToConfidentialVm::Resume() => {}
            ExposeToConfidentialVm::SbiHsmHartStart(v) => self.apply_sbi_hart_start(v),
            ExposeToConfidentialVm::InterProcessorInterrupt(v) => self.apply_inter_processor_interrupt(v),
            ExposeToConfidentialVm::SbiRemoteFenceI(v) => self.apply_remote_fence_i(v),
            ExposeToConfidentialVm::SbiRemoteSfenceVma(v) => self.apply_remote_sfence_vma(v),
            ExposeToConfidentialVm::SbiRemoteSfenceVmaAsid(v) => self.apply_remote_sfence_vma_asid(v),
        }
        core::ptr::addr_of!(self.confidential_hart_state) as usize
    }

    fn apply_inter_processor_interrupt(&mut self, _result: SbiIpi) {
        // IPI exposes itself as supervisor-level software interrupt this is the 2nd bit of the vsip controlled by the
        // hvip register. Check the RISC-V privileged specification for more information.
        const VSSIP: usize = 1 << 2; // virtual supervisor software interrupt pending bit in the hvip register
        self.confidential_hart_state.hvip |= VSSIP;
    }

    fn apply_remote_fence_i(&mut self, _result: SbiRemoteFenceI) {
        unsafe { core::arch::asm!("fence.i") };
    }

    fn apply_remote_sfence_vma(&mut self, _result: SbiRemoteSfenceVma) {
        // TODO: execute a more fine grained fence. Right now, we just do the full TLB flush
        unsafe { core::arch::asm!("sfence.vma") };
    }

    fn apply_remote_sfence_vma_asid(&mut self, _result: SbiRemoteSfenceVmaAsid) {
        // TODO: execute a more fine grained fence. Right now, we just do the full TLB flush
        unsafe { core::arch::asm!("sfence.vma") };
    }

    fn apply_sbi_hart_start(&mut self, result: SbiHsmHartStart) {
        self.confidential_hart_state.set_gpr(GpRegister::a1, self.confidential_hart_id());
        self.confidential_hart_state.set_gpr(GpRegister::a2, result.blob);
        self.confidential_hart_state.mepc = result.boot_code_address;
    }

    fn apply_sbi_result(&mut self, result: SbiResult) {
        self.confidential_hart_state.set_gpr(GpRegister::a0, result.a0());
        self.confidential_hart_state.set_gpr(GpRegister::a1, result.a1());
        self.confidential_hart_state.mepc += result.pc_offset();
    }

    fn apply_guest_load_page_fault_result(&mut self, result: GuestLoadPageFaultResult) {
        self.confidential_hart_state.set_gpr(result.result_gpr(), result.value());
        self.confidential_hart_state.mepc += result.instruction_length();
    }

    fn apply_guest_store_page_fault_result(&mut self, result: GuestStorePageFaultResult) {
        self.confidential_hart_state.mepc += result.instruction_length();
    }
}

// functions to expose portions of confidential virtual hart state
impl ConfidentialHart {
    pub fn trap_reason(&self) -> TrapReason {
        self.confidential_hart_state.trap_reason()
    }

    pub fn hypercall_request(&self) -> SbiRequest {
        SbiRequest::from_hart_state(&self.confidential_hart_state)
    }

    pub fn guest_load_page_fault_request(&self) -> Result<(GuestLoadPageFaultRequest, MmioLoadRequest), Error> {
        let mcause = riscv::register::mcause::read().code();
        let (instruction, instruction_length) = self.read_instruction();
        let gpr = crate::core::architecture::decode_result_register(instruction)?;
        let mtval = self.confidential_hart_state.mtval;
        let mtval2 = self.confidential_hart_state.mtval2;

        let load_fault_request = GuestLoadPageFaultRequest::new(instruction_length, gpr);
        let mmio_load_request = MmioLoadRequest::new(mcause, mtval, mtval2, instruction);

        Ok((load_fault_request, mmio_load_request))
    }

    pub fn guest_store_page_fault_request(&self) -> Result<(GuestStorePageFaultRequest, MmioStoreRequest), Error> {
        let mcause = riscv::register::mcause::read().code();
        let (instruction, instruction_length) = self.read_instruction();
        let gpr = crate::core::architecture::decode_result_register(instruction)?;
        let gpr_value = self.confidential_hart_state.gpr(gpr);
        let mtval = self.confidential_hart_state.mtval;
        let mtval2 = self.confidential_hart_state.mtval2;

        let guest_store_page_fault_request = GuestStorePageFaultRequest::new(instruction_length);
        let mmio_store_request = MmioStoreRequest::new(mcause, mtval, mtval2, instruction, gpr, gpr_value);

        Ok((guest_store_page_fault_request, mmio_store_request))
    }

    pub fn share_page_request(&self) -> Result<(SharePageRequest, SbiRequest), Error> {
        let shared_page_address = self.confidential_hart_state.gpr(GpRegister::a0);
        let share_page_request = SharePageRequest::new(shared_page_address)?;
        let sbi_request = SbiRequest::kvm_ace_page_in(shared_page_address);

        Ok((share_page_request, sbi_request))
    }

    pub fn sbi_ipi(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GpRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GpRegister::a1);
        InterHartRequest::InterProcessorInterrupt(SbiIpi::new(hart_mask, hart_mask_base))
    }

    pub fn sbi_hsm_hart_start(&self) -> SbiHsmHartStart {
        let confidential_hart_id = self.confidential_hart_state.gpr(GpRegister::a0);
        let boot_code_address = self.confidential_hart_state.gpr(GpRegister::a1);
        let blob = self.confidential_hart_state.gpr(GpRegister::a2);
        SbiHsmHartStart::new(confidential_hart_id, boot_code_address, blob)
    }

    pub fn sbi_remote_fence_i(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GpRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GpRegister::a1);
        InterHartRequest::SbiRemoteFenceI(SbiRemoteFenceI::new(hart_mask, hart_mask_base))
    }

    pub fn sbi_remote_sfence_vma(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GpRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GpRegister::a1);
        let start_address = self.confidential_hart_state.gpr(GpRegister::a2);
        let size = self.confidential_hart_state.gpr(GpRegister::a3);
        InterHartRequest::SbiRemoteSfenceVma(SbiRemoteSfenceVma::new(hart_mask, hart_mask_base, start_address, size))
    }

    pub fn sbi_remote_sfence_vma_asid(&self) -> InterHartRequest {
        let hart_mask = self.confidential_hart_state.gpr(GpRegister::a0);
        let hart_mask_base = self.confidential_hart_state.gpr(GpRegister::a1);
        let start_address = self.confidential_hart_state.gpr(GpRegister::a2);
        let size = self.confidential_hart_state.gpr(GpRegister::a3);
        let asid = self.confidential_hart_state.gpr(GpRegister::a4);
        InterHartRequest::SbiRemoteSfenceVmaAsid(SbiRemoteSfenceVmaAsid::new(
            hart_mask,
            hart_mask_base,
            start_address,
            size,
            asid,
        ))
    }

    fn read_instruction(&self) -> (usize, usize) {
        // mepc stores the virtual address of the instruction that caused trap. Setting
        // mstatus.MPRV bit allows reading the faulting instruction in memory using the
        // virtual address.
        let fault_instruction_virtual_address = self.confidential_hart_state.mepc as *const usize;
        let instruction = unsafe {
            riscv::register::mstatus::set_mprv();
            let instruction = fault_instruction_virtual_address.read_volatile();
            riscv::register::mstatus::clear_mprv();
            instruction
        };

        // We only expose the faulting instruction, which can be of different length.
        // Therefore, we must trim the read memory to this size by disabling unwanted
        // bits after learning what is the size of the fault instruction.
        let instruction_length = riscv_decode::instruction_length(instruction as u16);
        let mask = (1 << 8 * instruction_length) - 1;
        let instruction = (instruction & mask) as usize;

        (instruction, instruction_length)
    }
}
