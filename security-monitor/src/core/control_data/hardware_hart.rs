// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{GpRegister, HartArchitecturalState, TrapReason};
use crate::core::control_data::ConfidentialHart;
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, UnAllocated};
use crate::core::transformations::{
    ConvertToConfidentialVm, ExposeToHypervisor, GuestLoadPageFaultRequest, GuestLoadPageFaultResult, InterruptRequest, MmioLoadRequest,
    MmioStoreRequest, OpensbiRequest, ResumeRequest, SbiRequest, SbiResult, SbiVmRequest, SharePageResult, TerminateRequest,
};

#[repr(C)]
pub struct HardwareHart {
    // Careful, HardwareHart and ConfidentialHart must both start with the HartArchitecturalState element because based
    // on this we automatically calculate offsets of registers' and CSRs' for the asm code.
    pub(super) non_confidential_hart_state: HartArchitecturalState,
    // Memory protector that configures the hardware memory isolation component to allow only memory accesses
    // to the memory region owned by the hypervisor.
    hypervisor_memory_protector: HypervisorMemoryProtector,
    // A page containing the stack of the code executing within the given hart.
    pub(super) stack: Page<Allocated>,
    // The stack_address is redundant (we can learn the stack_address from the page assigned to the stack) but we need
    // it because this is the way to expose it to assembly
    pub(super) stack_address: usize,
    // We need to store the OpenSBI's mscratch value because OpenSBI uses mscratch to track some of its internal
    // data structures and our security monitor also uses mscratch to keep track of the address of the hart state
    // in memory.
    previous_mscratch: usize,
    // We keep the virtual hart that is associated with this hardware hart. The virtual hart can be 1) a dummy hart
    // in case there is any confidential VM's virtual hart associated to it, or 2) an confidential VM's virtual hart.
    // In the latter case, the hardware hart and confidential VM's control data swap their virtual harts (a dummy
    // hart with the confidential VM's virtual hart)
    pub(super) confidential_hart: ConfidentialHart,
}

impl HardwareHart {
    pub fn init(id: usize, stack: Page<UnAllocated>, hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self {
            non_confidential_hart_state: HartArchitecturalState::empty(id),
            hypervisor_memory_protector,
            stack_address: stack.end_address(),
            stack: stack.zeroize(),
            previous_mscratch: 0,
            confidential_hart: ConfidentialHart::dummy(id),
        }
    }

    pub fn address(&self) -> usize {
        core::ptr::addr_of!(self.non_confidential_hart_state) as usize
    }

    /// Calling OpenSBI handler to process the SBI call requires setting the mscratch register to a specific value which
    /// we replaced during the system initialization. We store the original mscratch value expected by the OpenSBI in
    /// the previous_mscratch field.
    pub fn swap_mscratch(&mut self) {
        let current_mscratch = riscv::register::mscratch::read();
        riscv::register::mscratch::write(self.previous_mscratch);
        self.previous_mscratch = current_mscratch;
    }

    pub fn confidential_hart(&self) -> &ConfidentialHart {
        &self.confidential_hart
    }

    pub fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        &mut self.confidential_hart
    }

    pub fn hypervisor_memory_protector(&self) -> &HypervisorMemoryProtector {
        &self.hypervisor_memory_protector
    }

    pub unsafe fn enable_hypervisor_memory_protector(&self) {
        self.hypervisor_memory_protector.enable(self.non_confidential_hart_state.hgatp)
    }
}

impl HardwareHart {
    pub fn apply(&mut self, transformation: &ExposeToHypervisor) {
        match transformation {
            ExposeToHypervisor::SbiRequest(v) => self.apply_sbi_request(v),
            ExposeToHypervisor::SbiVmRequest(v) => self.apply_sbi_vm_request(v),
            ExposeToHypervisor::SbiResult(v) => self.apply_sbi_result(v),
            ExposeToHypervisor::MmioLoadRequest(v) => self.apply_mmio_load_request(v),
            ExposeToHypervisor::MmioStoreRequest(v) => self.apply_mmio_store_request(v),
            ExposeToHypervisor::InterruptRequest(v) => self.apply_interrupt_request(v),
        }
    }

    fn apply_sbi_result(&mut self, result: &SbiResult) {
        self.non_confidential_hart_state.set_gpr(GpRegister::a0, result.a0());
        self.non_confidential_hart_state.set_gpr(GpRegister::a1, result.a1());
        self.non_confidential_hart_state.mepc += result.pc_offset();
    }

    fn apply_sbi_vm_request(&mut self, request: &SbiVmRequest) {
        const SCAUSE_EXCEPTION_VS_ECALL: usize = 10;

        self.non_confidential_hart_state.scause = SCAUSE_EXCEPTION_VS_ECALL;
        self.non_confidential_hart_state.sip |= 1 << SCAUSE_EXCEPTION_VS_ECALL;
        self.non_confidential_hart_state.sie |= 1 << SCAUSE_EXCEPTION_VS_ECALL;
        self.non_confidential_hart_state.sepc = request.sepc();

        let sbi_request = request.sbi_request();
        self.non_confidential_hart_state.set_gpr(GpRegister::a7, sbi_request.extension_id());
        self.non_confidential_hart_state.set_gpr(GpRegister::a6, sbi_request.function_id());
        self.non_confidential_hart_state.set_gpr(GpRegister::a0, sbi_request.a0());
        self.non_confidential_hart_state.set_gpr(GpRegister::a1, sbi_request.a1());
        self.non_confidential_hart_state.set_gpr(GpRegister::a2, sbi_request.a2());
        self.non_confidential_hart_state.set_gpr(GpRegister::a3, sbi_request.a3());
        self.non_confidential_hart_state.set_gpr(GpRegister::a4, sbi_request.a4());
        self.non_confidential_hart_state.set_gpr(GpRegister::a5, sbi_request.a5());

        self.apply_trap();
    }

    fn apply_sbi_request(&mut self, request: &SbiRequest) {
        const SCAUSE_EXCEPTION_VS_ECALL: usize = 10;

        self.non_confidential_hart_state.scause = SCAUSE_EXCEPTION_VS_ECALL;
        self.non_confidential_hart_state.sip |= 1 << SCAUSE_EXCEPTION_VS_ECALL;
        self.non_confidential_hart_state.sie |= 1 << SCAUSE_EXCEPTION_VS_ECALL;

        self.non_confidential_hart_state.set_gpr(GpRegister::a7, request.extension_id());
        self.non_confidential_hart_state.set_gpr(GpRegister::a6, request.function_id());
        self.non_confidential_hart_state.set_gpr(GpRegister::a0, request.a0());
        self.non_confidential_hart_state.set_gpr(GpRegister::a1, request.a1());
        self.non_confidential_hart_state.set_gpr(GpRegister::a2, request.a2());
        self.non_confidential_hart_state.set_gpr(GpRegister::a3, request.a3());
        self.non_confidential_hart_state.set_gpr(GpRegister::a4, request.a4());
        self.non_confidential_hart_state.set_gpr(GpRegister::a5, request.a5());

        self.apply_trap();
    }

    fn apply_mmio_load_request(&mut self, request: &MmioLoadRequest) {
        self.non_confidential_hart_state.scause = request.code();
        self.non_confidential_hart_state.sip |= 1 << request.code();
        self.non_confidential_hart_state.sie |= 1 << request.code();

        // KVM uses:
        //  - htval and stval to recreate the fault_addr
        //  - htinst to learn about faulting instructions
        self.non_confidential_hart_state.stval = request.stval();
        self.non_confidential_hart_state.htval = request.htval();

        // hack: we do not allow the hypervisor to look into the guest memory
        // but we have to inform him about the instruction that caused exception.
        // our approach is to expose this instruction via t6
        // TODO: consider using htinst register
        self.non_confidential_hart_state.set_gpr(GpRegister::t6, request.instruction());

        self.apply_trap();
    }

    fn apply_mmio_store_request(&mut self, request: &MmioStoreRequest) {
        self.non_confidential_hart_state.scause = request.code();
        self.non_confidential_hart_state.sip |= 1 << request.code();
        self.non_confidential_hart_state.sie |= 1 << request.code();

        // KVM uses:
        //  - htval and stval to recreate the fault_addr
        //  - htinst to learn about faulting instructions
        self.non_confidential_hart_state.stval = request.stval();
        self.non_confidential_hart_state.htval = request.htval();
        self.non_confidential_hart_state.set_gpr(request.gpr(), request.gpr_value());

        // hack: we do not allow the hypervisor to look into the guest memory
        // but we have to inform him about the instruction that caused exception.
        // our approach is to expose this instruction via t6
        // TODO: consider using htinst register
        self.non_confidential_hart_state.set_gpr(GpRegister::t6, request.instruction());

        self.apply_trap();
    }

    fn apply_interrupt_request(&mut self, request: &InterruptRequest) {
        const SCAUSE_INTERRUPT_BIT: usize = 63;
        self.non_confidential_hart_state.sip |= 1 << request.code();
        self.non_confidential_hart_state.sie |= 1 << request.code();
        self.non_confidential_hart_state.scause = request.code() | 1 << SCAUSE_INTERRUPT_BIT;
        self.apply_trap();
    }

    #[inline]
    fn apply_trap(&mut self) {
        const HSTATUS_SPV_BIT: usize = 7;
        const HSTATUS_GVA_BIT: usize = 6;
        const MSTATUS_SPP_BIT: usize = 8;
        const MSTATUS_SIE_BIT: usize = 1;
        const MSTATUS_MPV_BIT: usize = 39;
        const MSTATUS_MPP_BIT: usize = 11;
        const MSTATUS_MPIE_BIT: usize = 7;
        const MSTATUS_GVA_BIT: usize = 38;
        self.non_confidential_hart_state.mepc = riscv::register::stvec::read().bits();
        // let hypervisor think VS-mode executed
        self.non_confidential_hart_state.hstatus = self.non_confidential_hart_state.hstatus | (1 << HSTATUS_SPV_BIT);
        self.non_confidential_hart_state.mstatus = self.non_confidential_hart_state.mstatus | (1 << MSTATUS_SPP_BIT);
        // will disable virtualization (so HS not VS mode)
        self.non_confidential_hart_state.mstatus = self.non_confidential_hart_state.mstatus & !(1 << MSTATUS_MPV_BIT);
        self.non_confidential_hart_state.mstatus = self.non_confidential_hart_state.mstatus | (1 << MSTATUS_MPP_BIT);
        // disable interrupts
        self.non_confidential_hart_state.mstatus = self.non_confidential_hart_state.mstatus & !(1 << MSTATUS_MPIE_BIT);
        self.non_confidential_hart_state.mstatus = self.non_confidential_hart_state.mstatus & !(1 << MSTATUS_SIE_BIT);
        // set GVA
        if (self.non_confidential_hart_state.mstatus & (1 << MSTATUS_GVA_BIT)) > 0 {
            self.non_confidential_hart_state.hstatus = self.non_confidential_hart_state.hstatus | (1 << HSTATUS_GVA_BIT);
        } else {
            self.non_confidential_hart_state.hstatus = self.non_confidential_hart_state.hstatus & !(1 << HSTATUS_GVA_BIT);
        }
    }
}

impl HardwareHart {
    pub fn trap_reason(&self) -> TrapReason {
        self.non_confidential_hart_state.trap_reason()
    }

    pub fn convert_to_confidential_vm_request(&self) -> ConvertToConfidentialVm {
        ConvertToConfidentialVm::new(&self.non_confidential_hart_state)
    }

    pub fn hypercall_result(&self) -> SbiResult {
        SbiResult::ecall(&self.non_confidential_hart_state)
    }

    pub fn guest_load_page_fault_result(&self, request: GuestLoadPageFaultRequest) -> GuestLoadPageFaultResult {
        GuestLoadPageFaultResult::new(&self.non_confidential_hart_state, request)
    }

    pub fn sbi_vm_request(&self) -> SbiVmRequest {
        SbiVmRequest::from_hart_state(&self.non_confidential_hart_state)
    }

    pub fn resume_request(&self) -> ResumeRequest {
        let confidential_vm_id = self.non_confidential_hart_state.gpr(GpRegister::t0);
        let confidential_hart_id = self.non_confidential_hart_state.gpr(GpRegister::t1);
        ResumeRequest::new(confidential_vm_id, confidential_hart_id)
    }

    pub fn terminate_request(&self) -> TerminateRequest {
        let confidential_vm_id = self.non_confidential_hart_state.gpr(GpRegister::t0);
        TerminateRequest::new(confidential_vm_id)
    }

    pub fn share_page_result(&self) -> SharePageResult {
        let is_error = self.non_confidential_hart_state.gpr(GpRegister::a0);
        let hypervisor_page_address = self.non_confidential_hart_state.gpr(GpRegister::a1);
        SharePageResult::new(is_error, hypervisor_page_address)
    }

    pub fn opensbi_request(&self) -> OpensbiRequest {
        OpensbiRequest::new(&self.non_confidential_hart_state)
    }
}
