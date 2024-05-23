// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::*;

/// HartArchitecturalState is the dump state of the processor's core (hart).
/// It might represent the state of of software executing on real hardware hart, for example, architectural state of the hypervisor's thread
/// or confidential VM's thread.
#[repr(C)]
pub struct HartArchitecturalState {
    // gprs must be the first element in this structure because it is used to calculate the HartArchitecturalState
    // address in the memory. This address is used by the assembly code.
    gprs: GeneralPurposeRegisters,
    csrs: ControlStatusRegisters,
    fprs: FloatingPointRegisters,
}

impl HartArchitecturalState {
    pub fn empty() -> Self {
        Self { gprs: GeneralPurposeRegisters::empty(), csrs: ControlStatusRegisters::empty(), fprs: FloatingPointRegisters::empty() }
    }

    pub fn set_gprs(&mut self, gprs: GeneralPurposeRegisters) {
        self.gprs = gprs;
    }

    pub fn gprs(&self) -> &GeneralPurposeRegisters {
        &self.gprs
    }

    pub fn gprs_mut(&mut self) -> &mut GeneralPurposeRegisters {
        &mut self.gprs
    }

    pub fn fprs(&self) -> &FloatingPointRegisters {
        &self.fprs
    }

    pub fn fprs_mut(&mut self) -> &mut FloatingPointRegisters {
        &mut self.fprs
    }

    pub fn csrs(&self) -> &ControlStatusRegisters {
        &self.csrs
    }

    pub fn csrs_mut(&mut self) -> &mut ControlStatusRegisters {
        &mut self.csrs
    }
}

const fn hart_gpr_offset(index: GeneralPurposeRegister) -> usize {
    memoffset::offset_of!(HartArchitecturalState, gprs) + (index as usize) * core::mem::size_of::<u64>()
}

// The below constants are used by the context switch written in assembly.
// These offsets represent the offset of fields inside the hart state stored
// in the memory. They are calculated automatically using the aboce macros
// so, as developers, we do not have to worry about the order of fields inside
// the Rust structures representing hart state.
pub const HART_RA_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::ra);
pub const HART_SP_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::sp);
pub const HART_GP_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::gp);
pub const HART_TP_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::tp);
pub const HART_T0_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t0);
pub const HART_T1_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t1);
pub const HART_T2_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t2);
pub const HART_S0_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s0);
pub const HART_S1_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s1);
pub const HART_A0_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a0);
pub const HART_A1_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a1);
pub const HART_A2_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a2);
pub const HART_A3_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a3);
pub const HART_A4_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a4);
pub const HART_A5_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a5);
pub const HART_A6_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a6);
pub const HART_A7_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::a7);
pub const HART_S2_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s2);
pub const HART_S3_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s3);
pub const HART_S4_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s4);
pub const HART_S5_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s5);
pub const HART_S6_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s6);
pub const HART_S7_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s7);
pub const HART_S8_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s8);
pub const HART_S9_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s9);
pub const HART_S10_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s10);
pub const HART_S11_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::s11);
pub const HART_T3_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t3);
pub const HART_T4_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t4);
pub const HART_T5_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t5);
pub const HART_T6_OFFSET: usize = hart_gpr_offset(GeneralPurposeRegister::t6);
pub const HART_MEPC_OFFSET: usize =
    memoffset::offset_of!(HartArchitecturalState, csrs) + memoffset::offset_of!(ControlStatusRegisters, mepc);
pub const HART_MSTATUS_OFFSET: usize =
    memoffset::offset_of!(HartArchitecturalState, csrs) + memoffset::offset_of!(ControlStatusRegisters, mstatus);
