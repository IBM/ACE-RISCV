// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{FpRegisters, GpRegister, GpRegisters, CSR};

/// HartArchitecturalState is the dump state of the processor's core, called in RISC-V a hardware thread (HART).
#[repr(C)]
pub struct HartArchitecturalState {
    // gprs must be the first element in this structure because it is used to calculate the HartArchitecturalState
    // address in the memory. This address is used by the assembly code.
    pub gprs: GpRegisters,
    // floating-point related
    pub fprs: FpRegisters,
    pub fcsr: usize,
    // other data used by the security monitor
    pub id: usize,
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
    // timer-related
    // vstimecmp is provided by the Sstc (supervisor arch extensions for timecmp)
    pub vstimecmp: usize,
    pub htimedelta: usize,
    // virtualization-related
    pub hvip: usize,
    pub hgeip: usize,
    pub hie: usize,
    pub hgatp: usize,
    pub hedeleg: usize,
    pub hideleg: usize,
    pub htinst: usize,
    pub htval: usize,
    // S-mode
    pub sstatus: usize,
    // hstatus needed to control the virtualization bit
    pub hstatus: usize,
    pub sepc: usize,
    pub scounteren: usize, // not needed?
    pub sip: usize,
    pub sie: usize,
    pub scause: usize,
    pub stvec: usize,
    pub stval: usize,
    pub sscratch: usize,
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
            gprs: GpRegisters::empty(),
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
            vsatp: 0,
            hgatp: 0,
            fprs: FpRegisters::empty(),
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
}

impl HartArchitecturalState {
    pub fn gpr(&self, register: GpRegister) -> usize {
        self.gprs.get(register)
    }

    pub fn set_gpr(&mut self, register: GpRegister, value: usize) {
        self.gprs.set(register, value)
    }

    pub fn reset(&mut self) {
        self.gprs = GpRegisters::empty();
        self.fprs = FpRegisters::empty();
        self.fcsr = 0;
        self.htinst = 0;
        self.htval = 0;
        self.sepc = 0;
        self.scounteren = 0;
        self.vsie = 0;
        self.vstvec = 0;
        self.vsscratch = 0;
        self.vsepc = 0;
        self.vscause = 0;
        self.vstval = 0;
        self.hvip = 0;
        self.vsatp = 0;
        // set the timer interrupt to happen in 'infinity'
        self.vstimecmp = usize::MAX - 1;
        // TODO: set to the timer value observed during the confidential VM start?
        self.htimedelta = 0;
        // TODO: what should be the sstatus on reset?
        // self.sstatus = 0;
        self.vsstatus = 0;
    }
}
