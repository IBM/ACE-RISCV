// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::*;
use crate::core::architecture::{
    are_bits_enabled, ControlStatusRegisters, GeneralPurposeRegister, GeneralPurposeRegisters, HartArchitecturalState, TrapCause,
};
use crate::core::control_data::ConfidentialHart;
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, UnAllocated};
use crate::core::transformations::{
    EnabledInterrupts, ExposeToHypervisor, InjectedInterrupts, InterruptRequest, MmioLoadPending, MmioLoadRequest, MmioLoadResult,
    MmioStoreRequest, OpensbiRequest, OpensbiResult, PromoteToConfidentialVm, ResumeRequest, SbiRequest, SbiResult, SbiVmRequest,
    SharePageResult, TerminateRequest,
};

pub const HART_STACK_ADDRESS_OFFSET: usize = memoffset::offset_of!(HardwareHart, stack_address);

#[repr(C)]
pub struct HardwareHart {
    // Safety: HardwareHart and ConfidentialHart must both start with the HartArchitecturalState element because based
    // on this we automatically calculate offsets of registers' and CSRs' for the context switch implemented in assembly.
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
        let current_mscratch = self.csrs().mscratch.read();
        self.csrs().mscratch.set(self.previous_mscratch);
        self.previous_mscratch = current_mscratch;
    }

    pub fn confidential_hart(&self) -> &ConfidentialHart {
        &self.confidential_hart
    }

    pub fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        &mut self.confidential_hart
    }

    pub unsafe fn enable_hypervisor_memory_protector(&self) {
        self.hypervisor_memory_protector.enable(self.non_confidential_hart_state.csrs.hgatp.read_value())
    }
}

impl HardwareHart {
    pub fn apply(&mut self, transformation: &ExposeToHypervisor) {
        match transformation {
            ExposeToHypervisor::SbiRequest(v) => self.apply_sbi_request(v),
            ExposeToHypervisor::SbiVmRequest(v) => self.apply_sbi_vm_request(v),
            ExposeToHypervisor::SbiResult(v) => self.apply_sbi_result(v),
            ExposeToHypervisor::OpensbiResult(v) => self.apply_opensbi_result(v),
            ExposeToHypervisor::MmioLoadRequest(v) => self.apply_mmio_load_request(v),
            ExposeToHypervisor::MmioStoreRequest(v) => self.apply_mmio_store_request(v),
            ExposeToHypervisor::InterruptRequest(v) => self.apply_interrupt_request(v),
            ExposeToHypervisor::EnabledInterrupts(v) => self.apply_enabled_interrupts(v),
        }
    }

    pub fn apply_enabled_interrupts(&mut self, result: &EnabledInterrupts) {
        self.csrs().vsie.set(result.vsie());
    }

    fn apply_sbi_result(&mut self, result: &SbiResult) {
        self.gprs_mut().write(GeneralPurposeRegister::a0, result.a0());
        self.gprs_mut().write(GeneralPurposeRegister::a1, result.a1());
        self.non_confidential_hart_state.csrs.mepc.save_value(self.non_confidential_hart_state.csrs.mepc.read_value() + result.pc_offset());
    }

    fn apply_opensbi_result(&mut self, result: &OpensbiResult) {
        self.non_confidential_hart_state.csrs.mstatus.save_value(result.mstatus());
        self.non_confidential_hart_state.csrs.mepc.save_value(result.mepc());
        self.gprs_mut().write(GeneralPurposeRegister::a0, result.a0());
        self.gprs_mut().write(GeneralPurposeRegister::a1, result.a1());
    }

    fn apply_sbi_vm_request(&mut self, request: &SbiVmRequest) {
        self.csrs().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        self.gprs_mut().write(GeneralPurposeRegister::a7, request.sbi_request().extension_id());
        self.gprs_mut().write(GeneralPurposeRegister::a6, request.sbi_request().function_id());
        self.gprs_mut().write(GeneralPurposeRegister::a0, request.sbi_request().a0());
        self.gprs_mut().write(GeneralPurposeRegister::a1, request.sbi_request().a1());
        self.gprs_mut().write(GeneralPurposeRegister::a2, request.sbi_request().a2());
        self.gprs_mut().write(GeneralPurposeRegister::a3, request.sbi_request().a3());
        self.gprs_mut().write(GeneralPurposeRegister::a4, request.sbi_request().a4());
        self.gprs_mut().write(GeneralPurposeRegister::a5, request.sbi_request().a5());
        self.apply_trap(false);
    }

    fn apply_sbi_request(&mut self, request: &SbiRequest) {
        self.csrs().scause.set(CAUSE_VIRTUAL_SUPERVISOR_ECALL.into());
        self.gprs_mut().write(GeneralPurposeRegister::a7, request.extension_id());
        self.gprs_mut().write(GeneralPurposeRegister::a6, request.function_id());
        self.gprs_mut().write(GeneralPurposeRegister::a0, request.a0());
        self.gprs_mut().write(GeneralPurposeRegister::a1, request.a1());
        self.gprs_mut().write(GeneralPurposeRegister::a2, request.a2());
        self.gprs_mut().write(GeneralPurposeRegister::a3, request.a3());
        self.gprs_mut().write(GeneralPurposeRegister::a4, request.a4());
        self.gprs_mut().write(GeneralPurposeRegister::a5, request.a5());
        self.apply_trap(false);
    }

    fn apply_mmio_load_request(&mut self, request: &MmioLoadRequest) {
        self.csrs().scause.set(request.code());
        // KVM uses htval and stval to recreate the fault address
        self.csrs().stval.set(request.stval());
        self.csrs().htval.set(request.htval());
        // Hack: we do not allow the hypervisor to look into the guest memory but we have to inform him about the instruction that caused
        // exception. our approach is to expose this instruction via vsscratch. In future, we should move to RISC-V NACL extensions.
        self.csrs().vsscratch.set(request.instruction());
        self.apply_trap(true);
    }

    fn apply_mmio_store_request(&mut self, request: &MmioStoreRequest) {
        self.csrs().scause.set(request.code());
        // KVM uses htval and stval to recreate the fault address
        self.csrs().stval.set(request.stval());
        self.csrs().htval.set(request.htval());
        self.gprs_mut().write(request.gpr(), request.gpr_value());
        // Hack: we do not allow the hypervisor to look into the guest memory but we have to inform him about the instruction that caused
        // exception. our approach is to expose this instruction via vsscratch. In future, we should move to RISC-V NACL extensions.
        self.csrs().vsscratch.set(request.instruction());
        self.apply_trap(true);
    }

    fn apply_interrupt_request(&mut self, request: &InterruptRequest) {
        self.csrs().scause.set(request.code() | SCAUSE_INTERRUPT_MASK);
        self.apply_trap(false);
    }

    #[inline]
    fn apply_trap(&mut self, encoded_guest_virtual_address: bool) {
        if are_bits_enabled(self.csrs().stvec.read(), STVEC_MODE_VECTORED) {
            panic!("Not supported functionality: vectored traps");
        }

        // Set next mode to HS (see Table 8.8 in Riscv privilege spec 20211203)
        self.non_confidential_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPV);
        self.non_confidential_hart_state.csrs.mstatus.enable_bit_on_saved_value(CSR_MSTATUS_MPP);
        self.non_confidential_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);
        self.non_confidential_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_SIE);

        // Resume HS execution at its trap function
        self.csrs().sepc.set(self.non_confidential_hart_state.csrs.mepc.read_value());
        self.non_confidential_hart_state.csrs.mepc.save_value(self.csrs().stvec.read());

        // We trick the hypervisor to think that the trap comes directly from the VS-mode.
        self.non_confidential_hart_state.csrs.mstatus.enable_bit_on_saved_value(CSR_MSTATUS_SPP);
        self.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_SPV);
        self.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_SPVP);
        // According to the spec, hstatus:SPVP and sstatus.SPP have the same value when transitioning from VS to HS mode.
        self.csrs().sstatus.read_and_set_bit(CSR_SSTATUS_SPP);

        if encoded_guest_virtual_address {
            self.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_GVA);
        } else {
            self.csrs().hstatus.read_and_clear_bit(CSR_HSTATUS_GVA);
        }
    }
}

impl HardwareHart {
    pub fn gprs(&self) -> &GeneralPurposeRegisters {
        &self.non_confidential_hart_state.gprs
    }

    pub fn gprs_mut(&mut self) -> &mut GeneralPurposeRegisters {
        &mut self.non_confidential_hart_state.gprs
    }

    pub fn csrs(&self) -> &ControlStatusRegisters {
        &self.non_confidential_hart_state.csrs
    }

    pub fn hypervisor_hart_state(&self) -> &HartArchitecturalState {
        &self.non_confidential_hart_state
    }

    pub fn hypervisor_hart_state_mut(&mut self) -> &mut HartArchitecturalState {
        &mut self.non_confidential_hart_state
    }
}
