// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::CSR;
use crate::core::control_data::{ConfidentialHart, HypervisorHart};
use crate::core::memory_protector::HypervisorMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, UnAllocated};
use opensbi_sys::sbi_trap_regs;

unsafe extern "C" {
    /// Currently, we rely on OpenSBI to handle some of the interrupts or exceptions. Below function is the entry point
    /// to OpenSBI trap handler.
    fn sbi_trap_handler(regs: *mut sbi_trap_regs) -> *mut sbi_trap_regs;
}

pub const HART_STACK_ADDRESS_OFFSET: usize = memoffset::offset_of!(HardwareHart, stack_address);

/// Represents a state of a physical hart that executes in the security monitor. It is always associated with a hypervisor hart that made a
/// call to the security monitor.
///
/// There is exactly one instance of this structure created per physical hart during system initialization. We link the physical hart with
/// its instance of `HardwareHart` structure using `mscratch` register. See assembly code that implements the lightweight context switch.
#[repr(C)]
pub struct HardwareHart {
    // We store a hypervisor hart that was executing on this physical hart when making a call to the security monitor.
    hypervisor_hart: HypervisorHart,
    // We keep the confidential hart associated with this hardware hart. The virtual hart can be 1) a dummy hart
    // in case there is any confidential VM's virtual hart associated to it, or 2) an confidential VM's virtual hart.
    // In the latter case, the hardware hart and confidential VM's control data swap their virtual harts (a dummy
    // hart with the confidential VM's virtual hart)
    confidential_hart: ConfidentialHart,
    // A page containing the stack of the code executing within the given hart.
    stack: Page<Allocated>,
    // The stack_address is redundant (we can learn the stack_address from the page assigned for the stack) but we need
    // it because this is the way to expose it to assembly
    stack_address: usize,
    // We need to store the OpenSBI's mscratch value because OpenSBI uses mscratch to track some of its internal
    // data structures and our security monitor also uses mscratch to keep track of the address of the hart state
    // in memory.
    previous_mscratch: usize,
}

impl HardwareHart {
    /// Creates the instance of a state associated with the physical hart. Id is the unique physical hart identifier used to by hardware
    /// during inter process interrupts (IPIs), e.g., on RISC-V this will be a number reported by mhartid.
    pub fn init(id: usize, stack: Page<UnAllocated>, hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self {
            hypervisor_hart: HypervisorHart::new(hypervisor_memory_protector),
            confidential_hart: ConfidentialHart::dummy(id),
            stack_address: stack.end_address(),
            stack: stack.zeroize(),
            previous_mscratch: 0,
        }
    }

    // Safety: this function can be called only once during initialization. We cannot do it in constructor, because physical harts art not
    // initialized yet then.
    pub fn set_ace_mscratch(&mut self, value: usize) {
        self.previous_mscratch = CSR.mscratch.swap(value);
    }

    #[inline(always)]
    pub fn opensbi_context<F>(&mut self, function: F) -> Result<(), crate::error::Error>
    where F: FnOnce() -> Result<(), crate::error::Error> {
        let ace_mscratch = CSR.mscratch.swap(self.previous_mscratch);
        let result = function();
        CSR.mscratch.write(ace_mscratch);
        result
    }

    #[inline(always)]
    pub fn call_opensbi_trap_handler(&mut self) {
        // Safety: We play with fire here. We must make sure statically that the OpenSBI's input structure is bitwise same as the ACE's hart
        // state.
        let trap_regs = self.hypervisor_hart_mut().hypervisor_hart_state_mut() as *mut _ as *mut sbi_trap_regs;
        let _ = self.opensbi_context(|| {
            Ok(unsafe {
                sbi_trap_handler(trap_regs);
            })
        });
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
