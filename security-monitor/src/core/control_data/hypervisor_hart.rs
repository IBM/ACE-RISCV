// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::*;
use crate::core::architecture::{are_bits_enabled, ControlStatusRegisters, GeneralPurposeRegisters, HartArchitecturalState};
use crate::core::memory_protector::HypervisorMemoryProtector;

pub struct HypervisorHart {
    // Safety: HypervisorHart and ConfidentialHart must both start with the HartArchitecturalState element
    // because based on this we automatically calculate offsets of registers' and CSRs' for the asm code.
    hypervisor_hart_state: HartArchitecturalState,
    // Memory protector that configures the hardware memory isolation component to allow only memory accesses
    // to the memory region owned by the hypervisor.
    hypervisor_memory_protector: HypervisorMemoryProtector,
}

impl HypervisorHart {
    pub fn new(id: usize, hypervisor_memory_protector: HypervisorMemoryProtector) -> Self {
        Self { hypervisor_hart_state: HartArchitecturalState::empty(id), hypervisor_memory_protector }
    }

    pub fn gprs(&self) -> &GeneralPurposeRegisters {
        self.hypervisor_hart_state.gprs()
    }

    pub fn gprs_mut(&mut self) -> &mut GeneralPurposeRegisters {
        self.hypervisor_hart_state.gprs_mut()
    }

    pub fn csrs(&self) -> &ControlStatusRegisters {
        self.hypervisor_hart_state.csrs()
    }

    pub fn csrs_mut(&mut self) -> &mut ControlStatusRegisters {
        self.hypervisor_hart_state.csrs_mut()
    }

    pub fn hypervisor_hart_state(&self) -> &HartArchitecturalState {
        &self.hypervisor_hart_state
    }

    pub fn apply_trap(&mut self, encoded_guest_virtual_address: bool) {
        if are_bits_enabled(self.hypervisor_hart_state.csrs().stvec.read(), STVEC_MODE_VECTORED) {
            panic!("Not supported functionality: vectored traps");
        }

        // Set next mode to HS (see Table 8.8 in Riscv privilege spec 20211203)
        self.hypervisor_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPV);
        self.hypervisor_hart_state.csrs.mstatus.enable_bit_on_saved_value(CSR_MSTATUS_MPP);
        self.hypervisor_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_MPIE);
        self.hypervisor_hart_state.csrs.mstatus.disable_bit_on_saved_value(CSR_MSTATUS_SIE);

        // Resume HS execution at its trap function
        self.hypervisor_hart_state.csrs().sepc.set(self.hypervisor_hart_state.csrs.mepc.read_value());
        self.hypervisor_hart_state.csrs.mepc.save_value(self.hypervisor_hart_state.csrs().stvec.read());

        // We trick the hypervisor to think that the trap comes directly from the VS-mode.
        self.hypervisor_hart_state.csrs.mstatus.enable_bit_on_saved_value(CSR_MSTATUS_SPP);
        self.hypervisor_hart_state.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_SPV);
        self.hypervisor_hart_state.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_SPVP);
        // According to the spec, hstatus:SPVP and sstatus.SPP have the same value when transitioning from VS to HS mode.
        self.hypervisor_hart_state.csrs().sstatus.read_and_set_bit(CSR_SSTATUS_SPP);

        if encoded_guest_virtual_address {
            self.hypervisor_hart_state.csrs().hstatus.read_and_set_bit(CSR_HSTATUS_GVA);
        } else {
            self.hypervisor_hart_state.csrs().hstatus.read_and_clear_bit(CSR_HSTATUS_GVA);
        }
    }

    pub unsafe fn enable_hypervisor_memory_protector(&self) {
        self.hypervisor_memory_protector.enable(self.csrs().hgatp.read_value())
    }
}
