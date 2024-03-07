// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{FloatingPointRegisters, GeneralPurposeRegister, GeneralPurposeRegisters, CSR};

/// HartArchitecturalState is the dump state of the processor's core, called in RISC-V a hardware thread (HART).
#[repr(C)]
pub struct HartArchitecturalState {
    // gprs must be the first element in this structure because it is used to calculate the HartArchitecturalState
    // address in the memory. This address is used by the assembly code.
    pub gprs: GeneralPurposeRegisters,
    // floating-point related
    pub fprs: FloatingPointRegisters,
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
    pub hip: usize,
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

    pub fn store_processor_state_in_main_memory(&mut self) {
        // we not not store GPRs because assembly code does it
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

    pub fn load_processor_state_from_main_memory(&self) {
        // resume from where the other domain was interrupted - not needed since we reload mepc with assembly?
        CSR.mepc.set(self.mepc);
        CSR.mstatus.set(self.mstatus);
        CSR.mideleg.set(self.mideleg);
        CSR.medeleg.set(self.medeleg);
        // set the new trap vector so the code always trap in the security monitor in the correct handler
        CSR.mtvec.set(self.mtvec);
        // recover interrupt configuration from the hypervisor execution. delegations (`mideleg`) must be already recovered!
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
        // recover interrupt configuration from the hypervisor execution. delegations (`hideleg`) must be already recovered!
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

    pub fn reset(&mut self) {
        self.gprs = GeneralPurposeRegisters::empty();
        self.fprs = FloatingPointRegisters::empty();
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
