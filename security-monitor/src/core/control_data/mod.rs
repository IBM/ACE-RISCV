// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use confidential_hart::ConfidentialHart;
pub use confidential_vm::{ConfidentialVm, ConfidentialVmId};
pub use hardware_hart::HardwareHart;
pub use storage::{ControlData, CONTROL_DATA};

use crate::core::hart::{GpRegister, HartState};

mod confidential_hart;
mod confidential_vm;
mod hardware_hart;
mod storage;

const fn hart_gpr_offset(index: GpRegister) -> usize {
    memoffset::offset_of!(HardwareHart, non_confidential_hart_state)
        + memoffset::offset_of!(HartState, gprs)
        + (index as usize) * core::mem::size_of::<u64>()
}

const fn hart_fpr_offset(index: usize) -> usize {
    memoffset::offset_of!(HardwareHart, non_confidential_hart_state)
        + memoffset::offset_of!(HartState, fprs)
        + index * core::mem::size_of::<u64>()
}

macro_rules! hart_csr_offset {
    ($reg:tt) => {
        memoffset::offset_of!(HardwareHart, non_confidential_hart_state) + memoffset::offset_of!(HartState, $reg)
    };
}

macro_rules! hart_element_offset {
    ($reg:tt) => {
        memoffset::offset_of!(HardwareHart, $reg)
    };
}

// The below constants are used by the context switch written in assembly.
// These offsets represent the offset of fields inside the hart state stored
// in the memory. They are calculated automatically using the aboce macros
// so, as developers, we do not have to worry about the order of fields inside
// the Rust structures representing hart state.
pub const HART_RA_OFFSET: usize = hart_gpr_offset(GpRegister::ra);
pub const HART_SP_OFFSET: usize = hart_gpr_offset(GpRegister::sp);
pub const HART_GP_OFFSET: usize = hart_gpr_offset(GpRegister::gp);
pub const HART_TP_OFFSET: usize = hart_gpr_offset(GpRegister::tp);
pub const HART_T0_OFFSET: usize = hart_gpr_offset(GpRegister::t0);
pub const HART_T1_OFFSET: usize = hart_gpr_offset(GpRegister::t1);
pub const HART_T2_OFFSET: usize = hart_gpr_offset(GpRegister::t2);
pub const HART_S0_OFFSET: usize = hart_gpr_offset(GpRegister::s0);
pub const HART_S1_OFFSET: usize = hart_gpr_offset(GpRegister::s1);
pub const HART_A0_OFFSET: usize = hart_gpr_offset(GpRegister::a0);
pub const HART_A1_OFFSET: usize = hart_gpr_offset(GpRegister::a1);
pub const HART_A2_OFFSET: usize = hart_gpr_offset(GpRegister::a2);
pub const HART_A3_OFFSET: usize = hart_gpr_offset(GpRegister::a3);
pub const HART_A4_OFFSET: usize = hart_gpr_offset(GpRegister::a4);
pub const HART_A5_OFFSET: usize = hart_gpr_offset(GpRegister::a5);
pub const HART_A6_OFFSET: usize = hart_gpr_offset(GpRegister::a6);
pub const HART_A7_OFFSET: usize = hart_gpr_offset(GpRegister::a7);
pub const HART_S2_OFFSET: usize = hart_gpr_offset(GpRegister::s2);
pub const HART_S3_OFFSET: usize = hart_gpr_offset(GpRegister::s3);
pub const HART_S4_OFFSET: usize = hart_gpr_offset(GpRegister::s4);
pub const HART_S5_OFFSET: usize = hart_gpr_offset(GpRegister::s5);
pub const HART_S6_OFFSET: usize = hart_gpr_offset(GpRegister::s6);
pub const HART_S7_OFFSET: usize = hart_gpr_offset(GpRegister::s7);
pub const HART_S8_OFFSET: usize = hart_gpr_offset(GpRegister::s8);
pub const HART_S9_OFFSET: usize = hart_gpr_offset(GpRegister::s9);
pub const HART_S10_OFFSET: usize = hart_gpr_offset(GpRegister::s10);
pub const HART_S11_OFFSET: usize = hart_gpr_offset(GpRegister::s11);
pub const HART_T3_OFFSET: usize = hart_gpr_offset(GpRegister::t3);
pub const HART_T4_OFFSET: usize = hart_gpr_offset(GpRegister::t4);
pub const HART_T5_OFFSET: usize = hart_gpr_offset(GpRegister::t5);
pub const HART_T6_OFFSET: usize = hart_gpr_offset(GpRegister::t6);

pub const HART_F0_OFFSET: usize = hart_fpr_offset(0);
pub const HART_F1_OFFSET: usize = hart_fpr_offset(1);
pub const HART_F2_OFFSET: usize = hart_fpr_offset(2);
pub const HART_F3_OFFSET: usize = hart_fpr_offset(3);
pub const HART_F4_OFFSET: usize = hart_fpr_offset(4);
pub const HART_F5_OFFSET: usize = hart_fpr_offset(5);
pub const HART_F6_OFFSET: usize = hart_fpr_offset(6);
pub const HART_F7_OFFSET: usize = hart_fpr_offset(7);
pub const HART_F8_OFFSET: usize = hart_fpr_offset(8);
pub const HART_F9_OFFSET: usize = hart_fpr_offset(9);
pub const HART_F10_OFFSET: usize = hart_fpr_offset(10);
pub const HART_F11_OFFSET: usize = hart_fpr_offset(11);
pub const HART_F12_OFFSET: usize = hart_fpr_offset(12);
pub const HART_F13_OFFSET: usize = hart_fpr_offset(13);
pub const HART_F14_OFFSET: usize = hart_fpr_offset(14);
pub const HART_F15_OFFSET: usize = hart_fpr_offset(15);
pub const HART_F16_OFFSET: usize = hart_fpr_offset(16);
pub const HART_F17_OFFSET: usize = hart_fpr_offset(17);
pub const HART_F18_OFFSET: usize = hart_fpr_offset(18);
pub const HART_F19_OFFSET: usize = hart_fpr_offset(19);
pub const HART_F20_OFFSET: usize = hart_fpr_offset(20);
pub const HART_F21_OFFSET: usize = hart_fpr_offset(21);
pub const HART_F22_OFFSET: usize = hart_fpr_offset(22);
pub const HART_F23_OFFSET: usize = hart_fpr_offset(23);
pub const HART_F24_OFFSET: usize = hart_fpr_offset(24);
pub const HART_F25_OFFSET: usize = hart_fpr_offset(25);
pub const HART_F26_OFFSET: usize = hart_fpr_offset(26);
pub const HART_F27_OFFSET: usize = hart_fpr_offset(27);
pub const HART_F28_OFFSET: usize = hart_fpr_offset(28);
pub const HART_F29_OFFSET: usize = hart_fpr_offset(29);
pub const HART_F30_OFFSET: usize = hart_fpr_offset(30);
pub const HART_F31_OFFSET: usize = hart_fpr_offset(31);
pub const HART_FCSR_OFFSET: usize = hart_csr_offset!(fcsr);

pub const HART_SSTATUS_OFFSET: usize = hart_csr_offset!(sstatus);
pub const HART_HSTATUS_OFFSET: usize = hart_csr_offset!(hstatus);
pub const HART_SEPC_OFFSET: usize = hart_csr_offset!(sepc);
pub const HART_VSSTATUS_OFFSET: usize = hart_csr_offset!(vsstatus);
pub const HART_VSIE_OFFSET: usize = hart_csr_offset!(vsie);
pub const HART_VSTVEC_OFFSET: usize = hart_csr_offset!(vstvec);
pub const HART_VSSCRATCH_OFFSET: usize = hart_csr_offset!(vsscratch);
pub const HART_VSEPC_OFFSET: usize = hart_csr_offset!(vsepc);
pub const HART_VSCAUSE_OFFSET: usize = hart_csr_offset!(vscause);
pub const HART_VSTVAL_OFFSET: usize = hart_csr_offset!(vstval);
pub const HART_HVIP_OFFSET: usize = hart_csr_offset!(hvip);
pub const HART_HTVAL_OFFSET: usize = hart_csr_offset!(htval);
pub const HART_VSATP_OFFSET: usize = hart_csr_offset!(vsatp);
pub const HART_HGATP_OFFSET: usize = hart_csr_offset!(hgatp);
pub const HART_HEDELEG_OFFSET: usize = hart_csr_offset!(hedeleg);
pub const HART_HIDELEG_OFFSET: usize = hart_csr_offset!(hideleg);
pub const HART_HTINST_OFFSET: usize = hart_csr_offset!(htinst);
pub const HART_MEPC_OFFSET: usize = hart_csr_offset!(mepc);
pub const HART_MSTATUS_OFFSET: usize = hart_csr_offset!(mstatus);
pub const HART_MIDELEG_OFFSET: usize = hart_csr_offset!(mideleg);
pub const HART_MEDELEG_OFFSET: usize = hart_csr_offset!(medeleg);
pub const HART_MIE_OFFSET: usize = hart_csr_offset!(mie);
pub const HART_MIP_OFFSET: usize = hart_csr_offset!(mip);
pub const HART_MTINST_OFFSET: usize = hart_csr_offset!(mtinst);
pub const HART_MTVAL_OFFSET: usize = hart_csr_offset!(mtval);
pub const HART_MTVAL2_OFFSET: usize = hart_csr_offset!(mtval2);
pub const HART_SIP_OFFSET: usize = hart_csr_offset!(sip);
pub const HART_SIE_OFFSET: usize = hart_csr_offset!(sie);
pub const HART_SCAUSE_OFFSET: usize = hart_csr_offset!(scause);
pub const HART_STVAL_OFFSET: usize = hart_csr_offset!(stval);
pub const HART_SSCRATCH_OFFSET: usize = hart_csr_offset!(sscratch);
pub const HART_SCOUNTEREN_OFFSET: usize = hart_csr_offset!(scounteren);

pub const HART_STACK_ADDRESS_OFFSET: usize = hart_element_offset!(stack_address);
