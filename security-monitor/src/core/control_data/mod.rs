// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use confidential_hart::ConfidentialHart;
pub use confidential_vm::ConfidentialVm;
pub use confidential_vm_id::ConfidentialVmId;
pub use confidential_vm_measurement::ConfidentialVmMeasurement;
pub use hardware_hart::HardwareHart;
pub use storage::{ControlData, CONTROL_DATA};

use crate::core::architecture::{GpRegister, HartArchitecturalState};

mod confidential_hart;
mod confidential_vm;
mod confidential_vm_id;
mod confidential_vm_measurement;
mod hardware_hart;
mod storage;

const fn hart_gpr_offset(index: GpRegister) -> usize {
    memoffset::offset_of!(HardwareHart, non_confidential_hart_state)
        + memoffset::offset_of!(HartArchitecturalState, gprs)
        + (index as usize) * core::mem::size_of::<u64>()
}

macro_rules! hart_csr_offset {
    ($reg:tt) => {
        memoffset::offset_of!(HardwareHart, non_confidential_hart_state) + memoffset::offset_of!(HartArchitecturalState, $reg)
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

pub const HART_MEPC_OFFSET: usize = hart_csr_offset!(mepc);
pub const HART_MSTATUS_OFFSET: usize = hart_csr_offset!(mstatus);

pub const HART_STACK_ADDRESS_OFFSET: usize = hart_element_offset!(stack_address);
