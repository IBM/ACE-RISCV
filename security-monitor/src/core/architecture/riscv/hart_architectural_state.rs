// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::*;

/// HartArchitecturalState is the dump state of the processor's core, called in RISC-V a hardware thread (HART).
#[repr(C)]
pub struct HartArchitecturalState {
    // gprs must be the first element in this structure because it is used to calculate the HartArchitecturalState
    // address in the memory. This address is used by the assembly code.
    pub gprs: GeneralPurposeRegisters,
    // other data used by the security monitor
    pub id: usize,

    // M-mode related
    pub mepc: usize,
    pub mstatus: usize,
    pub medeleg: usize,
    pub mideleg: usize,
    pub mie: usize,
    pub mip: usize,
    pub mtinst: usize,
    pub mtval: usize,
    pub mtval2: usize,
    pub mtvec: usize,
    // S-mode
    pub sstatus: usize,
    pub hstatus: usize,
    pub sepc: usize,
    pub scounteren: usize,
    pub sip: usize,
    pub sie: usize,
    pub scause: usize,
    pub stvec: usize,
    pub stval: usize,
    pub sscratch: usize,
    // virtualization-related
    pub hvip: usize,
    pub hgeip: usize,
    pub hie: usize,
    pub hip: usize,
    pub hgatp: usize,
    pub hedeleg: usize,
    pub hideleg: usize,
    pub htinst: usize,
    pub htval: usize,
    // vstimecmp is provided by the Sstc (supervisor arch extensions for timecmp)
    pub vstimecmp: usize,
    pub htimedelta: usize,
    // VS-mode
    pub vsstatus: usize,
    pub vsie: usize,
    pub vsip: usize,
    pub vstvec: usize,
    pub vsscratch: usize,
    pub vsepc: usize,
    pub vscause: usize,
    pub vstval: usize,
    pub vsatp: usize,
    // floating-point related
    pub fprs: FloatingPointRegisters,
    pub fcsr: usize,
}

impl HartArchitecturalState {
    pub fn from_existing(id: usize, existing: &HartArchitecturalState) -> HartArchitecturalState {
        HartArchitecturalState {
            id,
            gprs: existing.gprs.clone(),
            // M-mode
            mepc: CSR.mepc.read(),
            medeleg: CSR.medeleg.read(),
            mideleg: CSR.mideleg.read(),
            mie: CSR.mie.read(),
            mip: CSR.mip.read(),
            mstatus: CSR.mstatus.read(),
            mtinst: CSR.mtinst.read(),
            mtval: CSR.mtval.read(),
            mtval2: CSR.mtval2.read(),
            mtvec: CSR.mtvec.read(),
            // S-mode
            sstatus: CSR.sstatus.read(),
            sepc: CSR.sepc.read(),
            scounteren: CSR.scounteren.read(),
            sip: CSR.sip.read(),
            sie: CSR.sie.read(),
            scause: CSR.scause.read(),
            stvec: CSR.stvec.read(),
            stval: CSR.stval.read(),
            sscratch: CSR.sscratch.read(),
            // HS-mode
            hstatus: CSR.hstatus.read(),
            hedeleg: CSR.hedeleg.read(),
            hideleg: CSR.hideleg.read(),
            htinst: CSR.htinst.read(),
            htval: CSR.htval.read(),
            hvip: CSR.hvip.read(),
            hgeip: CSR.hgeip.read(),
            hie: CSR.hie.read(),
            hip: CSR.hip.read(),
            hgatp: CSR.hgatp.read(),
            // VS-mode
            vsstatus: CSR.vsstatus.read(),
            vsie: CSR.vsie.read(),
            vsip: CSR.vsip.read(),
            vstvec: CSR.vstvec.read(),
            vsscratch: CSR.vsscratch.read(),
            vsepc: CSR.vsepc.read(),
            vscause: CSR.vscause.read(),
            vstval: CSR.vstval.read(),
            vsatp: CSR.vsatp.read(),
            // timer-related
            vstimecmp: CSR.vstimecmp.read(),
            htimedelta: CSR.htimedelta.read(),
            // F-extension
            fprs: existing.fprs.clone(),
            fcsr: CSR.fcsr.read(),
        }
    }

    pub fn empty(id: usize) -> HartArchitecturalState {
        HartArchitecturalState {
            id,
            gprs: GeneralPurposeRegisters::empty(),
            sstatus: 0,
            hstatus: 0,
            hedeleg: 0,
            hideleg: 0,
            htinst: 0,
            htval: 0,
            sepc: 0,
            scounteren: 0,
            vsstatus: 0,
            vsie: 0,
            vsip: 0,
            vstvec: 0,
            vsscratch: 0,
            vsepc: 0,
            vscause: 0,
            vstval: 0,
            vstimecmp: usize::MAX - 1,
            htimedelta: 0,
            hvip: 0,
            hgeip: 0,
            hie: 0,
            hip: 0,
            vsatp: 0,
            hgatp: 0,
            fprs: FloatingPointRegisters::empty(),
            fcsr: 0,
            sip: 0,
            sie: 0,
            scause: 0,
            stval: 0,
            stvec: 0,
            sscratch: 0,
            mepc: 0,
            medeleg: 0,
            mideleg: 0,
            mie: 0,
            mip: 0,
            mstatus: 0,
            mtinst: 0,
            mtval: 0,
            mtval2: 0,
            mtvec: 0,
        }
    }

    pub fn save_control_status_registers_in_main_memory(&mut self) {
        self.mepc = CSR.mepc.read();
        self.mstatus = CSR.mstatus.read();
        self.mideleg = CSR.mideleg.read();
        self.medeleg = CSR.medeleg.read();
        self.mtvec = CSR.mtvec.read();
        self.mie = CSR.mie.read();
        // S-mode
        self.sstatus = CSR.sstatus.read();
        self.sepc = CSR.sepc.read();
        self.scounteren = CSR.scounteren.read();
        self.sip = CSR.sip.read();
        self.sie = CSR.sie.read();
        self.scause = CSR.scause.read();
        self.stvec = CSR.stvec.read();
        self.stval = CSR.stval.read();
        self.sscratch = CSR.sscratch.read();
        // HS-mode
        self.hstatus = CSR.hstatus.read();
        self.hedeleg = CSR.hedeleg.read();
        self.hideleg = CSR.hideleg.read();
        self.htinst = CSR.htinst.read();
        self.htval = CSR.htval.read();
        self.hvip = CSR.hvip.read();
        self.hgeip = CSR.hgeip.read();
        self.hie = CSR.hie.read();
        self.hip = CSR.hip.read();
        self.hgatp = CSR.hgatp.read();
        // VS-mode
        self.vsstatus = CSR.vsstatus.read();
        self.vsie = CSR.vsie.read();
        self.vsip = CSR.vsip.read();
        self.vstvec = CSR.vstvec.read();
        self.vsscratch = CSR.vsscratch.read();
        self.vsepc = CSR.vsepc.read();
        self.vscause = CSR.vscause.read();
        self.vstval = CSR.vstval.read();
        self.vsatp = CSR.vsatp.read();
        // timer-related
        self.vstimecmp = CSR.vstimecmp.read();
        self.htimedelta = CSR.htimedelta.read();
        // F-extension
        // self.fprs = existing.fprs.clone();
        self.fcsr = CSR.fcsr.read();
    }

    pub fn restore_control_status_registers_from_main_memory(&self) {
        CSR.mepc.set(self.mepc);
        CSR.mstatus.set(self.mstatus);
        CSR.mideleg.set(self.mideleg);
        CSR.medeleg.set(self.medeleg);
        CSR.mtvec.set(self.mtvec);
        CSR.mie.set(self.mie);
        // S-mode
        CSR.sstatus.set(self.sstatus);
        CSR.sepc.set(self.sepc);
        CSR.scounteren.set(self.scounteren);
        CSR.sip.set(self.sip);
        CSR.sie.set(self.sie);
        CSR.scause.set(self.scause);
        CSR.stvec.set(self.stvec);
        CSR.stval.set(self.stval);
        CSR.sscratch.set(self.sscratch);
        // HS-mode
        CSR.hstatus.set(self.hstatus);
        CSR.hedeleg.set(self.hedeleg);
        CSR.hideleg.set(self.hideleg);
        CSR.htinst.set(self.htinst);
        CSR.htval.set(self.htval);
        // CSR.hvip.set(to.hvip);
        // CSR.hgeip.set(self.hgeip);
        CSR.hie.set(self.hie);
        // CSR.hip.set(self.hip);
        CSR.hgatp.set(self.hgatp);
        // VS-mode
        CSR.vsstatus.set(self.vsstatus);
        CSR.vsie.set(self.vsie);
        CSR.vsip.set(self.vsip);
        CSR.vstvec.set(self.vstvec);
        CSR.vsscratch.set(self.vsscratch);
        CSR.vsepc.set(self.vsepc);
        CSR.vscause.set(self.vscause);
        CSR.vstval.set(self.vstval);
        CSR.vsatp.set(self.vsatp);
        // timer-related
        CSR.vstimecmp.set(self.vstimecmp);
        CSR.htimedelta.set(self.htimedelta);
        // F-extension
        // self.fprs = existing.fprs.clone();
        CSR.fcsr.set(self.fcsr);
    }
}

impl HartArchitecturalState {
    pub fn gpr(&self, register: GeneralPurposeRegister) -> usize {
        self.gprs.get(register)
    }

    pub fn set_gpr(&mut self, register: GeneralPurposeRegister, value: usize) {
        self.gprs.set(register, value)
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
pub const HART_MEPC_OFFSET: usize = memoffset::offset_of!(HartArchitecturalState, mepc);
pub const HART_MSTATUS_OFFSET: usize = memoffset::offset_of!(HartArchitecturalState, mstatus);
