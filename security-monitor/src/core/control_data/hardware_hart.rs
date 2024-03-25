// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::mmio::requests::{MmioLoadRequest, MmioStoreRequest};
use crate::core::architecture::specification::*;
use crate::core::architecture::{
    are_bits_enabled, ControlStatusRegisters, GeneralPurposeRegister, GeneralPurposeRegisters, HartArchitecturalState, CSR,
};
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, UnAllocated};
use crate::core::transformations::{
    EnabledInterrupts, ExposeToHypervisor, InterruptRequest, OpensbiResult, SbiRequest, SbiResult, SbiVmRequest,
};

pub const HART_STACK_ADDRESS_OFFSET: usize = memoffset::offset_of!(HardwareHart, stack_address);

#[repr(C)]
pub struct HardwareHart {
    // We store a hypervisor hart that was executing on this physical hart when making a call to the security monitor.
    hypervisor_hart: HypervisorHart,
    // A page containing the stack of the code executing within the given hart.
    stack: Page<Allocated>,
    // The stack_address is redundant (we can learn the stack_address from the page assigned to the stack) but we need
    // it because this is the way to expose it to assembly
    stack_address: usize,
    // We need to store the OpenSBI's mscratch value because OpenSBI uses mscratch to track some of its internal
    // data structures and our security monitor also uses mscratch to keep track of the address of the hart state
    // in memory.
    previous_mscratch: usize,
    // We keep the confidential hart associated with this hardware hart. The virtual hart can be 1) a dummy hart
    // in case there is any confidential VM's virtual hart associated to it, or 2) an confidential VM's virtual hart.
    // In the latter case, the hardware hart and confidential VM's control data swap their virtual harts (a dummy
    // hart with the confidential VM's virtual hart)
    confidential_hart: ConfidentialHart,
}

impl HardwareHart {
    pub fn init(id: usize, stack: Page<UnAllocated>, hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self {
            hypervisor_hart: HypervisorHart::new(id, hypervisor_memory_protector),
            stack_address: stack.end_address(),
            stack: stack.zeroize(),
            previous_mscratch: 0,
            confidential_hart: ConfidentialHart::dummy(id),
        }
    }

    pub fn address(&self) -> usize {
        core::ptr::addr_of!(self.hypervisor_hart) as usize
        // + memoffset::offset_of!(HardwareHart, stack_address)
    }

    /// Calling OpenSBI handler to process the SBI call requires setting the mscratch register to a specific value which
    /// we replaced during the system initialization. We store the original mscratch value expected by the OpenSBI in
    /// the previous_mscratch field.
    pub fn swap_mscratch(&mut self) {
        let previous_mscratch = self.previous_mscratch;
        let current_mscratch = CSR.mscratch.read();
        CSR.mscratch.set(previous_mscratch);
        self.previous_mscratch = current_mscratch;
    }

    pub fn confidential_hart(&self) -> &ConfidentialHart {
        &self.confidential_hart
    }

    pub fn confidential_hart_mut(&mut self) -> &mut ConfidentialHart {
        &mut self.confidential_hart
    }

    pub fn hypervisor_hart(&self) -> &HypervisorHart {
        &self.hypervisor_hart
    }

    pub fn hypervisor_hart_mut(&mut self) -> &mut HypervisorHart {
        &mut self.hypervisor_hart
    }
}

impl HardwareHart {
    pub fn apply(&mut self, transformation: &ExposeToHypervisor) {
        match transformation {
            ExposeToHypervisor::SbiRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::SbiVmRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::SbiResult(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::OpensbiResult(v) => v.apply_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::MmioLoadRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::MmioStoreRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
            ExposeToHypervisor::InterruptRequest(v) => v.declassify_to_hypervisor_hart(self.hypervisor_hart_mut()),
        }
    }
}
