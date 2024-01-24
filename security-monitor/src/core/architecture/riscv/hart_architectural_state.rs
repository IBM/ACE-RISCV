// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::{FpRegisters, GpRegister, GpRegisters, TrapReason};

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
    pub vstvec: usize,
    pub vsscratch: usize,
    pub vsepc: usize,
    pub vscause: usize,
    pub vstval: usize,
    pub vsatp: usize,
    // virtualization-related
    pub hvip: usize,
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
}

impl HartArchitecturalState {
    pub fn from_existing(id: usize, existing: &HartArchitecturalState) -> HartArchitecturalState {
        HartArchitecturalState {
            id,
            gprs: existing.gprs.clone(),
            // M-mode
            mepc: existing.mepc,
            medeleg: existing.medeleg,
            mideleg: existing.mideleg,
            mie: existing.mie,
            mip: existing.mip,
            mstatus: existing.mstatus,
            mtinst: existing.mtinst,
            mtval: existing.mtval,
            mtval2: existing.mtval2,
            // S-mode
            sstatus: existing.sstatus,
            sepc: existing.sepc,
            scounteren: existing.scounteren,
            sip: existing.sip,
            sie: existing.sie,
            scause: existing.scause,
            stvec: existing.stvec,
            stval: existing.stval,
            sscratch: existing.sscratch,
            // HS-mode
            hstatus: existing.hstatus,
            hedeleg: existing.hedeleg,
            hideleg: existing.hideleg,
            htinst: existing.htinst,
            htval: existing.htval,
            hvip: existing.hvip,
            hgatp: existing.hgatp,
            // VS-mode
            vsstatus: existing.vsstatus,
            vsie: existing.vsie,
            vstvec: existing.vstvec,
            vsscratch: existing.vsscratch,
            vsepc: existing.vsepc,
            vscause: existing.vscause,
            vstval: existing.vstval,
            vsatp: existing.vsatp,
            // F-extension
            fprs: existing.fprs.clone(),
            fcsr: existing.fcsr,
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
            vstvec: 0,
            vsscratch: 0,
            vsepc: 0,
            vscause: 0,
            vstval: 0,
            hvip: 0,
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
        // TODO: what should be the sstatus on reset?
        // self.sstatus = 0;
        self.vsstatus = 0;
    }

    pub fn trap_reason(&self) -> TrapReason {
        TrapReason::from_hart_state(self)
    }
}

impl core::fmt::Debug for HartArchitecturalState {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "hart_id: {}, ", self.id)?;
        GpRegisters::iter().try_for_each(|x| -> core::fmt::Result {
            write!(f, "x{:02}={:08x}, ", x, self.gprs.0[x])?;
            if x % 8 == 7 {
                write!(f, "\n")?;
            }
            Ok(())
        })?;
        FpRegisters::iter().try_for_each(|x| -> core::fmt::Result {
            write!(f, "f{:02}={:08x}, ", x, self.fprs.0[x])?;
            if x % 8 == 7 {
                write!(f, "\n")?;
            }
            Ok(())
        })?;
        write!(f, "sstatus: {:08x}, ", self.sstatus)?;
        write!(f, "hstatus: {:08x}, ", self.hstatus)?;
        write!(f, "sepc: {:08x}, ", self.sepc)?;
        write!(f, "scounteren: {:08x}, ", self.scounteren)?;
        write!(f, "\n")?;
        write!(f, "hgatp: {:08x}, ", self.hgatp)?;
        write!(f, "sip: {:08x}, ", self.sip)?;
        write!(f, "sie: {:08x}, ", self.sie)?;
        write!(f, "scause: {:08x}, ", self.scause)?;
        write!(f, "\n")?;
        write!(f, "vsstatus: {:08x}, ", self.vsstatus)?;
        write!(f, "vsie: {:08x}, ", self.vsie)?;
        write!(f, "vstvec: {:08x}, ", self.vstvec)?;
        write!(f, "vsscratch: {:08x}, ", self.vsscratch)?;
        write!(f, "\n")?;
        write!(f, "vsepc: {:08x}, ", self.vsepc)?;
        write!(f, "vscause: {:08x}, ", self.vscause)?;
        write!(f, "vstval: {:08x}, ", self.vstval)?;
        write!(f, "hvip: {:08x}, ", self.hvip)?;
        write!(f, "\n")?;
        write!(f, "vsatp: {:08x}, ", self.vsatp)?;
        write!(f, "fcsr: {:08x}, ", self.fcsr)?;
        write!(f, "mideleg: {:08x}, ", self.mideleg)?;
        write!(f, "medeleg: {:08x}, ", self.medeleg)?;
        write!(f, "mie: {:08x}, ", self.mie)?;
        write!(f, "mip: {:08x}, ", self.mip)?;
        Ok(())
    }
}
