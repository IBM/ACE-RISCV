// SPDX-FileCopyrightText: 2023 Rivos Inc.
// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
// This implementation is based on the code from Rivos. We just use a subset of functionalities and CSRs because we do not need all of them.
// https://github.com/rivosinc/salus/blob/fd06d5959fd81c02b8763c1922f36cc0ebe7d301/riscv-regs/src/csrs/csr_access.rs#L47
#![allow(unused)]
pub use super::specification::*;
use crate::core::architecture::NaclSharedMemory;
use core::arch::asm;

pub struct ControlStatusRegisters {
    pub mepc: ReadWriteRiscvCsr<CSR_MEPC>,
    pub mcause: ReadWriteRiscvCsr<CSR_MCAUSE>,
    pub medeleg: ReadWriteRiscvCsr<CSR_MEDELEG>,
    pub mideleg: ReadWriteRiscvCsr<CSR_MIDELEG>,
    pub mie: ReadWriteRiscvCsr<CSR_MIE>,
    pub mip: ReadRiscvCsr<CSR_MIP>,
    pub mstatus: ReadWriteRiscvCsr<CSR_MSTATUS>,
    pub mtinst: ReadWriteRiscvCsr<CSR_MTINST>,
    pub mtval: ReadWriteRiscvCsr<CSR_MTVAL>,
    pub mtval2: ReadWriteRiscvCsr<CSR_MTVAL2>,
    pub mtvec: ReadWriteRiscvCsr<CSR_MTVEC>,
    pub mscratch: ReadWriteRiscvCsr<CSR_MSCRATCH>,
    pub mhartid: ReadRiscvCsr<CSR_MHARTID>,
    // S-mode
    pub sstatus: ReadWriteRiscvCsr<CSR_SSTATUS>,
    pub sie: ReadWriteRiscvCsr<CSR_SIE>,
    pub stvec: ReadWriteRiscvCsr<CSR_STVEC>,
    pub scounteren: ReadWriteRiscvCsr<CSR_SCOUNTEREN>,
    pub senvcfg: ReadWriteRiscvCsr<CSR_SENVCFG>,
    pub sscratch: ReadWriteRiscvCsr<CSR_SSCRATCH>,
    pub sepc: ReadWriteRiscvCsr<CSR_SEPC>,
    pub scause: ReadWriteRiscvCsr<CSR_SCAUSE>,
    pub stval: ReadWriteRiscvCsr<CSR_STVAL>,
    pub sip: ReadWriteRiscvCsr<CSR_SIP>,
    pub satp: ReadWriteRiscvCsr<CSR_SATP>,
    // S-mode Debug extension
    pub scontext: ReadWriteRiscvCsr<CSR_SCONTEXT>,
    pub stimecmp: ReadWriteRiscvCsr<CSR_STIMECMP>,
    // HS-mode
    pub hstatus: ReadWriteRiscvCsr<CSR_HSTATUS>,
    pub hedeleg: ReadWriteRiscvCsr<CSR_HEDELEG>,
    pub hideleg: ReadWriteRiscvCsr<CSR_HIDELEG>,
    pub hie: ReadWriteRiscvCsr<CSR_HIE>,
    pub hcounteren: ReadWriteRiscvCsr<CSR_HCOUNTEREN>,
    pub hgeie: ReadWriteRiscvCsr<CSR_HGEIE>,
    pub htval: ReadWriteRiscvCsr<CSR_HTVAL>,
    pub hip: ReadWriteRiscvCsr<CSR_HIP>,
    pub hvip: ReadWriteRiscvCsr<CSR_HVIP>,
    pub htinst: ReadWriteRiscvCsr<CSR_HTINST>,
    pub hgeip: ReadWriteRiscvCsr<CSR_HGEIP>,
    pub henvcfg: ReadWriteRiscvCsr<CSR_HENVCFG>,
    pub hgatp: ReadWriteRiscvCsr<CSR_HGATP>,
    // HS-mode Debug
    pub hcontext: ReadWriteRiscvCsr<CSR_HCONTEXT>,
    pub htimedelta: ReadWriteRiscvCsr<CSR_HTIMEDELTA>,
    // VS-mode
    pub vsstatus: ReadWriteRiscvCsr<CSR_VSSTATUS>,
    pub vsie: ReadWriteRiscvCsr<CSR_VSIE>,
    pub vsip: ReadWriteRiscvCsr<CSR_VSIP>,
    pub vstvec: ReadWriteRiscvCsr<CSR_VSTVEC>,
    pub vsscratch: ReadWriteRiscvCsr<CSR_VSSCRATCH>,
    pub vsepc: ReadWriteRiscvCsr<CSR_VSEPC>,
    pub vscause: ReadWriteRiscvCsr<CSR_VSCAUSE>,
    pub vstval: ReadWriteRiscvCsr<CSR_VSTVAL>,
    pub vsatp: ReadWriteRiscvCsr<CSR_VSATP>,
    // timer-related
    pub vstimecmp: ReadWriteRiscvCsr<CSR_VSTIMECMP>,
    // F-extension
    pub fflags: ReadWriteRiscvCsr<CSR_FFLAGS>,
    pub frm: ReadWriteRiscvCsr<CSR_FRM>,
    pub fcsr: ReadWriteRiscvCsr<CSR_FCSR>,
    // V-extension
}

impl ControlStatusRegisters {
    pub fn empty() -> Self {
        let mut csrs = Self {
            mepc: ReadWriteRiscvCsr::new(),
            mcause: ReadWriteRiscvCsr::new(),
            medeleg: ReadWriteRiscvCsr::new(),
            mideleg: ReadWriteRiscvCsr::new(),
            mie: ReadWriteRiscvCsr::new(),
            mip: ReadRiscvCsr::new(),
            mstatus: ReadWriteRiscvCsr::new(),
            mtinst: ReadWriteRiscvCsr::new(),
            mtval: ReadWriteRiscvCsr::new(),
            mtval2: ReadWriteRiscvCsr::new(),
            mtvec: ReadWriteRiscvCsr::new(),
            mscratch: ReadWriteRiscvCsr::new(),
            mhartid: ReadRiscvCsr::new(),
            // S-mode
            sstatus: ReadWriteRiscvCsr::new(),
            sie: ReadWriteRiscvCsr::new(),
            stvec: ReadWriteRiscvCsr::new(),
            scounteren: ReadWriteRiscvCsr::new(),
            senvcfg: ReadWriteRiscvCsr::new(),
            sscratch: ReadWriteRiscvCsr::new(),
            sepc: ReadWriteRiscvCsr::new(),
            scause: ReadWriteRiscvCsr::new(),
            stval: ReadWriteRiscvCsr::new(),
            sip: ReadWriteRiscvCsr::new(),
            satp: ReadWriteRiscvCsr::new(),
            scontext: ReadWriteRiscvCsr::new(),
            stimecmp: ReadWriteRiscvCsr::new(),
            // HS-mode
            hstatus: ReadWriteRiscvCsr::new(),
            hedeleg: ReadWriteRiscvCsr::new(),
            hideleg: ReadWriteRiscvCsr::new(),
            hie: ReadWriteRiscvCsr::new(),
            hcounteren: ReadWriteRiscvCsr::new(),
            hgeie: ReadWriteRiscvCsr::new(),
            htval: ReadWriteRiscvCsr::new(),
            hip: ReadWriteRiscvCsr::new(),
            hvip: ReadWriteRiscvCsr::new(),
            htinst: ReadWriteRiscvCsr::new(),
            hgeip: ReadWriteRiscvCsr::new(),
            henvcfg: ReadWriteRiscvCsr::new(),
            hgatp: ReadWriteRiscvCsr::new(),
            hcontext: ReadWriteRiscvCsr::new(),
            htimedelta: ReadWriteRiscvCsr::new(),
            // VS-mode
            vsstatus: ReadWriteRiscvCsr::new(),
            vsie: ReadWriteRiscvCsr::new(),
            vsip: ReadWriteRiscvCsr::new(),
            vstvec: ReadWriteRiscvCsr::new(),
            vsscratch: ReadWriteRiscvCsr::new(),
            vsepc: ReadWriteRiscvCsr::new(),
            vscause: ReadWriteRiscvCsr::new(),
            vstval: ReadWriteRiscvCsr::new(),
            vsatp: ReadWriteRiscvCsr::new(),
            // timer-related
            vstimecmp: ReadWriteRiscvCsr::new(),
            // F-extension
            fflags: ReadWriteRiscvCsr::new(),
            frm: ReadWriteRiscvCsr::new(),
            fcsr: ReadWriteRiscvCsr::new(),
            // V-extension
        };
        csrs.vstimecmp.save_value(usize::MAX - 1);
        csrs
    }

    pub fn save_in_main_memory(&mut self) {
        self.mepc.save();
        self.mcause.save();
        self.medeleg.save();
        self.mideleg.save();
        self.mie.save();
        self.mstatus.save();
        self.mtinst.save();
        self.mtval.save();
        self.mtval2.save();
        self.mtvec.save();
        self.mscratch.save();
        // S-mode
        self.sstatus.save();
        self.sie.save();
        self.stvec.save();
        self.scounteren.save();
        self.senvcfg.save();
        self.sscratch.save();
        self.sepc.save();
        self.scause.save();
        self.stval.save();
        self.sip.save();
        self.satp.save();
        // Only if debug extension is implemented by hardware
        // self.scontext.save();
        self.stimecmp.save();
        // HS-mode
        self.hstatus.save();
        self.hedeleg.save();
        self.hideleg.save();
        self.hie.save();
        self.hcounteren.save();
        self.hgeie.save();
        self.htval.save();
        self.hip.save();
        self.hvip.save();
        self.htinst.save();
        self.hgeip.save();
        self.henvcfg.save();
        self.hgatp.save();
        // Only if debug extension is implemented by hardware
        // self.hcontext.save();
        self.htimedelta.save();
        // VS-mode
        self.vsstatus.save();
        self.vsie.save();
        self.vsip.save();
        self.vstvec.save();
        self.vsscratch.save();
        self.vsepc.save();
        self.vscause.save();
        self.vstval.save();
        self.vsatp.save();
        // timer-related
        self.vstimecmp.save();
    }

    pub fn restore_from_main_memory(&self) {
        self.mepc.restore();
        self.mcause.restore();
        self.medeleg.restore();
        self.mideleg.restore();
        self.mie.restore();
        self.mstatus.restore();
        self.mtinst.restore();
        self.mtval.restore();
        self.mtval2.restore();
        self.mtvec.restore();
        // S-mode
        self.sstatus.restore();
        self.sie.restore();
        self.stvec.restore();
        self.scounteren.restore();
        self.senvcfg.restore();
        self.sscratch.restore();
        self.sepc.restore();
        self.scause.restore();
        self.stval.restore();
        self.sip.restore();
        self.satp.restore();
        // Only if debug extension is implemented by hardware
        // self.scontext.restore();
        // Only if timer extension
        // self.stimecmp.restore();
        // HS-mode
        self.hstatus.restore();
        self.hedeleg.restore();
        self.hideleg.restore();
        self.hie.restore();
        self.hcounteren.restore();
        self.hgeie.restore();
        self.htval.restore();
        // self.hip.restore();
        // self.hvip.restore();
        self.htinst.restore();
        // self.hgeip.restore();
        self.henvcfg.restore();
        self.hgatp.restore();
        // Only if debug extension is implemented by hardware
        // self.hcontext.restore();
        self.htimedelta.restore();
        // VS-mode
        self.vsstatus.restore();
        self.vsie.restore();
        self.vsip.restore();
        self.vstvec.restore();
        self.vsscratch.restore();
        self.vsepc.restore();
        self.vscause.restore();
        self.vstval.restore();
        self.vsatp.restore();
        // timer-related
        self.vstimecmp.restore();
        // F-extension
        if (self.mstatus.read() & SR_FS) > 0 {
            self.fflags.restore();
            self.frm.restore();
            self.fcsr.restore();
        }
    }
}

pub struct ControlStatusRegister {
    pub mhartid: ReadWriteRiscvCsr<CSR_MHARTID>,
    pub mvendorid: ReadWriteRiscvCsr<CSR_MVENDORID>,
    pub marchid: ReadWriteRiscvCsr<CSR_MARCHID>,
    pub mimpid: ReadWriteRiscvCsr<CSR_MIMPID>,
    pub mscratch: ReadWriteRiscvCsr<CSR_MSCRATCH>,
    pub hgatp: ReadWriteRiscvCsr<CSR_HGATP>,
    pub pmpcfg0: ReadWriteRiscvCsr<CSR_PMPCFG0>,
    pub pmpaddr0: ReadWriteRiscvCsr<CSR_PMPADDR0>,
    pub pmpaddr1: ReadWriteRiscvCsr<CSR_PMPADDR1>,
}

pub const CSR: &ControlStatusRegister = &ControlStatusRegister {
    mhartid: ReadWriteRiscvCsr::new(),
    mvendorid: ReadWriteRiscvCsr::new(),
    marchid: ReadWriteRiscvCsr::new(),
    mimpid: ReadWriteRiscvCsr::new(),
    mscratch: ReadWriteRiscvCsr::new(),
    hgatp: ReadWriteRiscvCsr::new(),
    pmpcfg0: ReadWriteRiscvCsr::new(),
    pmpaddr0: ReadWriteRiscvCsr::new(),
    pmpaddr1: ReadWriteRiscvCsr::new(),
};

#[derive(Copy, Clone)]
pub struct ReadWriteRiscvCsr<const V: u16>(usize);

impl<const V: u16> ReadWriteRiscvCsr<V> {
    pub const fn new() -> Self {
        ReadWriteRiscvCsr(0)
    }

    pub fn save(&mut self) {
        self.0 = self.read();
    }

    pub fn save_value(&mut self, value: usize) {
        self.0 = value;
    }

    pub fn restore(&self) {
        self.set(self.0);
    }

    pub fn read_value(&self) -> usize {
        self.0
    }

    pub fn restore_from_nacl(&mut self, nacl_shared_memory: &NaclSharedMemory) {
        self.0 = nacl_shared_memory.csr(V.into());
    }

    #[inline]
    pub fn disable_bit_on_saved_value(&mut self, bit_index: usize) {
        self.disable_bits_on_saved_value(1 << bit_index);
    }

    #[inline]
    pub fn disable_bits_on_saved_value(&mut self, bit_mask: usize) {
        self.0 &= !bit_mask;
    }

    #[inline]
    pub fn enable_bit_on_saved_value(&mut self, bit_index: usize) {
        self.enable_bits_on_saved_value(1 << bit_index);
    }

    #[inline]
    pub fn enable_bits_on_saved_value(&mut self, bit_mask: usize) {
        self.0 |= bit_mask;
    }

    #[inline]
    pub fn read(&self) -> usize {
        let r: usize;
        unsafe {
            asm!("csrr {rd}, {csr}", rd = out(reg) r, csr = const V);
        }
        r
    }

    #[inline]
    pub fn set(&self, val_to_set: usize) {
        unsafe {
            asm!("csrw {csr}, {rs}", rs = in(reg) val_to_set, csr = const V);
        }
    }

    #[inline]
    pub fn read_and_set_bit(&self, bit: usize) -> usize {
        self.read_and_set_bits(1 << bit)
    }

    #[inline]
    pub fn read_and_set_bits(&self, bitmask: usize) -> usize {
        let r: usize;
        unsafe {
            asm!("csrrs {rd}, {csr}, {rs1}",
                 rd = out(reg) r,
                 csr = const V,
                 rs1 = in(reg) bitmask);
        }
        r
    }

    #[inline]
    pub fn read_and_clear_bit(&self, bit: usize) -> usize {
        self.read_and_clear_bits(1 << bit)
    }

    #[inline]
    pub fn read_and_clear_bits(&self, bitmask: usize) -> usize {
        let r: usize;
        unsafe {
            asm!("csrrc {rd}, {csr}, {rs1}",
                 rd = out(reg) r,
                 csr = const V,
                 rs1 = in(reg) bitmask);
        }
        r
    }
}

#[derive(Copy, Clone)]
pub struct ReadRiscvCsr<const V: u16>(usize);

impl<const V: u16> ReadRiscvCsr<V> {
    pub const fn new() -> Self {
        Self(0)
    }

    #[inline]
    pub fn read(&self) -> usize {
        let r: usize;
        unsafe {
            asm!("csrr {rd}, {csr}", rd = out(reg) r, csr = const V);
        }
        r
    }
}

#[repr(usize)]
#[derive(Clone, Copy, Debug)]
pub enum HgatpMode {
    Sv57x4 = 10,
}

impl HgatpMode {
    fn code(self) -> usize {
        self as usize
    }

    fn from_code(code: usize) -> Option<Self> {
        match code {
            10 => Some(HgatpMode::Sv57x4),
            _ => None,
        }
    }
}

pub struct Hgatp {
    bits: usize,
}

impl Hgatp {
    const HGATP64_MODE_SHIFT: usize = 60;
    const HGATP64_VMID_SHIFT: usize = 44;
    const PAGE_SHIFT: usize = 12;
    const HGATP_PPN_MASK: usize = 0x0000FFFFFFFFFFF;

    pub fn from(bits: usize) -> Self {
        Self { bits }
    }

    /// Returns the contents of the register as raw bits
    #[inline]
    pub fn bits(&self) -> usize {
        self.bits
    }

    pub fn address(&self) -> usize {
        (self.bits & Self::HGATP_PPN_MASK) << Self::PAGE_SHIFT
    }

    pub fn mode(&self) -> Option<HgatpMode> {
        HgatpMode::from_code((self.bits >> Self::HGATP64_MODE_SHIFT) & 0b1111)
    }

    pub fn new(address: usize, mode: HgatpMode, vmid: usize) -> Self {
        let ppn = (address >> Self::PAGE_SHIFT) & Self::HGATP_PPN_MASK;
        Self { bits: (vmid << Self::HGATP64_VMID_SHIFT) | (mode.code() << Self::HGATP64_MODE_SHIFT) | ppn }
    }
}
