// SPDX-FileCopyrightText: 2023 Rivos Inc.
// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
// This implementation is based on the code from Rivos. We just use a subset of functionalities and CSRs because we do not need all of them.
// https://github.com/rivosinc/salus/blob/fd06d5959fd81c02b8763c1922f36cc0ebe7d301/riscv-regs/src/csrs/csr_access.rs#L47
#![allow(unused)]
pub use super::specification::*;
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
    pub sepc: ReadWriteRiscvCsr<CSR_SEPC>,
    pub scounteren: ReadWriteRiscvCsr<CSR_SCOUNTEREN>,
    pub sip: ReadWriteRiscvCsr<CSR_SIP>,
    pub sie: ReadWriteRiscvCsr<CSR_SIE>,
    pub scause: ReadWriteRiscvCsr<CSR_SCAUSE>,
    pub stvec: ReadWriteRiscvCsr<CSR_STVEC>,
    pub stval: ReadWriteRiscvCsr<CSR_STVAL>,
    pub sscratch: ReadWriteRiscvCsr<CSR_SSCRATCH>,
    pub stimecmp: ReadWriteRiscvCsr<CSR_STIMECMP>,
    // HS-mode
    pub hstatus: ReadWriteRiscvCsr<CSR_HSTATUS>,
    pub hedeleg: ReadWriteRiscvCsr<CSR_HEDELEG>,
    pub hideleg: ReadWriteRiscvCsr<CSR_HIDELEG>,
    pub htinst: ReadWriteRiscvCsr<CSR_HTINST>,
    pub htval: ReadWriteRiscvCsr<CSR_HTVAL>,
    pub hvip: ReadWriteRiscvCsr<CSR_HVIP>,
    pub hgeip: ReadWriteRiscvCsr<CSR_HGEIP>,
    pub hie: ReadWriteRiscvCsr<CSR_HIE>,
    pub hip: ReadWriteRiscvCsr<CSR_HIP>,
    pub hgatp: ReadWriteRiscvCsr<CSR_HGATP>,
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
    pub htimedelta: ReadWriteRiscvCsr<CSR_HTIMEDELTA>,
    // F-extension
    pub fcsr: ReadWriteRiscvCsr<CSR_FCSR>,
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
            sepc: ReadWriteRiscvCsr::new(),
            scounteren: ReadWriteRiscvCsr::new(),
            sip: ReadWriteRiscvCsr::new(),
            sie: ReadWriteRiscvCsr::new(),
            scause: ReadWriteRiscvCsr::new(),
            stvec: ReadWriteRiscvCsr::new(),
            stval: ReadWriteRiscvCsr::new(),
            sscratch: ReadWriteRiscvCsr::new(),
            stimecmp: ReadWriteRiscvCsr::new(),
            // HS-mode
            hstatus: ReadWriteRiscvCsr::new(),
            hedeleg: ReadWriteRiscvCsr::new(),
            hideleg: ReadWriteRiscvCsr::new(),
            htinst: ReadWriteRiscvCsr::new(),
            htval: ReadWriteRiscvCsr::new(),
            hvip: ReadWriteRiscvCsr::new(),
            hgeip: ReadWriteRiscvCsr::new(),
            hie: ReadWriteRiscvCsr::new(),
            hip: ReadWriteRiscvCsr::new(),
            hgatp: ReadWriteRiscvCsr::new(),
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
            htimedelta: ReadWriteRiscvCsr::new(),
            // F-extension
            fcsr: ReadWriteRiscvCsr::new(),
        };
        csrs.vstimecmp.save_value(usize::MAX - 1);
        csrs
    }

    pub fn copy(&self) -> Self {
        let mut csrs = Self::empty();
        csrs.mepc.save_value(self.mepc.read_value());
        csrs.mcause.save_value(self.mcause.read_value());
        csrs.medeleg.save_value(self.medeleg.read_value());
        csrs.mideleg.save_value(self.mideleg.read_value());
        csrs.mie.save_value(self.mie.read_value());
        csrs.mstatus.save_value(self.mstatus.read_value());
        csrs.mtinst.save_value(self.mtinst.read_value());
        csrs.mtval.save_value(self.mtval.read_value());
        csrs.mtval2.save_value(self.mtval2.read_value());
        csrs.mtvec.save_value(self.mtvec.read_value());
        csrs.mscratch.save_value(self.mscratch.read_value());
        // S-mode
        csrs.sstatus.save_value(self.sstatus.read_value());
        csrs.sepc.save_value(self.sepc.read_value());
        csrs.scounteren.save_value(self.scounteren.read_value());
        csrs.sip.save_value(self.sip.read_value());
        csrs.sie.save_value(self.sie.read_value());
        csrs.scause.save_value(self.scause.read_value());
        csrs.stvec.save_value(self.stvec.read_value());
        csrs.stval.save_value(self.stval.read_value());
        csrs.sscratch.save_value(self.sscratch.read_value());
        csrs.stimecmp.save_value(self.stimecmp.read_value());
        // HS-mode
        csrs.hstatus.save_value(self.hstatus.read_value());
        csrs.hedeleg.save_value(self.hedeleg.read_value());
        csrs.hideleg.save_value(self.hideleg.read_value());
        csrs.htinst.save_value(self.htinst.read_value());
        csrs.htval.save_value(self.htval.read_value());
        csrs.hvip.save_value(self.hvip.read_value());
        csrs.hgeip.save_value(self.hgeip.read_value());
        csrs.hie.save_value(self.hie.read_value());
        csrs.hip.save_value(self.hip.read_value());
        csrs.hgatp.save_value(self.hgatp.read_value());
        // VS-mode
        csrs.vsstatus.save_value(self.vsstatus.read_value());
        csrs.vsie.save_value(self.vsie.read_value());
        csrs.vsip.save_value(self.vsip.read_value());
        csrs.vstvec.save_value(self.vstvec.read_value());
        csrs.vsscratch.save_value(self.vsscratch.read_value());
        csrs.vsepc.save_value(self.vsepc.read_value());
        csrs.vscause.save_value(self.vscause.read_value());
        csrs.vstval.save_value(self.vstval.read_value());
        csrs.vsatp.save_value(self.vsatp.read_value());
        // timer-related
        csrs.vstimecmp.save_value(self.vstimecmp.read_value());
        csrs.htimedelta.save_value(self.htimedelta.read_value());
        // F-extension
        csrs.fcsr.save_value(self.fcsr.read_value());
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
        self.sepc.save();
        self.scounteren.save();
        self.sip.save();
        self.sie.save();
        self.scause.save();
        self.stvec.save();
        self.stval.save();
        self.sscratch.save();
        self.stimecmp.save();
        // HS-mode
        self.hstatus.save();
        self.hedeleg.save();
        self.hideleg.save();
        self.htinst.save();
        self.htval.save();
        self.hvip.save();
        self.hgeip.save();
        self.hie.save();
        self.hip.save();
        self.hgatp.save();
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
        self.htimedelta.save();
        // F-extension
        self.fcsr.save();
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
        self.sepc.restore();
        self.scounteren.restore();
        self.sip.restore();
        self.sie.restore();
        self.scause.restore();
        self.stvec.restore();
        self.stval.restore();
        self.sscratch.restore();
        // self.stimecmp.restore();
        // HS-mode
        self.hstatus.restore();
        self.hedeleg.restore();
        self.hideleg.restore();
        self.htinst.restore();
        self.htval.restore();
        self.hie.restore();
        self.hgatp.restore();
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
        self.htimedelta.restore();
        // F-extension
        self.fcsr.restore();
    }
}

pub struct ControlStatusRegister {
    pub mhartid: ReadWriteRiscvCsr<CSR_MHARTID>,
    pub mscratch: ReadWriteRiscvCsr<CSR_MSCRATCH>,
    pub hgatp: ReadWriteRiscvCsr<CSR_HGATP>,
    pub pmpcfg0: ReadWriteRiscvCsr<CSR_PMPCFG0>,
    pub pmpaddr0: ReadWriteRiscvCsr<CSR_PMPADDR0>,
    pub pmpaddr1: ReadWriteRiscvCsr<CSR_PMPADDR1>,
}

pub const CSR: &ControlStatusRegister = &ControlStatusRegister {
    mhartid: ReadWriteRiscvCsr::new(),
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
