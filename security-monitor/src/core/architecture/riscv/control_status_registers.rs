// SPDX-FileCopyrightText: 2023 Rivos Inc.
// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
// This implementation is based on the code from Rivos. We just use a subset of functionalities and CSRs because we do not need all of them.
// https://github.com/rivosinc/salus/blob/fd06d5959fd81c02b8763c1922f36cc0ebe7d301/riscv-regs/src/csrs/csr_access.rs#L47
#![allow(unused)]
pub use super::specification::*;
use core::arch::asm;

pub struct ControlStatusRegister {
    pub mepc: ReadWriteRiscvCsr<CSR_MEPC>,
    pub mcause: ReadWriteRiscvCsr<CSR_MCAUSE>,
    pub medeleg: ReadWriteRiscvCsr<CSR_MEDELEG>,
    pub mideleg: ReadWriteRiscvCsr<CSR_MIDELEG>,
    pub mie: ReadWriteRiscvCsr<CSR_MIE>,
    pub mip: ReadWriteRiscvCsr<CSR_MIP>,
    pub mstatus: ReadWriteRiscvCsr<CSR_MSTATUS>,
    pub mtinst: ReadWriteRiscvCsr<CSR_MTINST>,
    pub mtval: ReadWriteRiscvCsr<CSR_MTVAL>,
    pub mtval2: ReadWriteRiscvCsr<CSR_MTVAL2>,
    pub mtvec: ReadWriteRiscvCsr<CSR_MTVEC>,
    pub mscratch: ReadWriteRiscvCsr<CSR_MSCRATCH>,
    pub mhartid: ReadWriteRiscvCsr<CSR_MHARTID>,
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
    // PMPs
    pub pmpcfg0: ReadWriteRiscvCsr<CSR_PMPCFG0>,
    pub pmpaddr0: ReadWriteRiscvCsr<CSR_PMPADDR0>,
    pub pmpaddr1: ReadWriteRiscvCsr<CSR_PMPADDR1>,
}

pub const CSR: &ControlStatusRegister = &ControlStatusRegister {
    mepc: ReadWriteRiscvCsr::new(),
    mcause: ReadWriteRiscvCsr::new(),
    medeleg: ReadWriteRiscvCsr::new(),
    mideleg: ReadWriteRiscvCsr::new(),
    mie: ReadWriteRiscvCsr::new(),
    mip: ReadWriteRiscvCsr::new(),
    mstatus: ReadWriteRiscvCsr::new(),
    mtinst: ReadWriteRiscvCsr::new(),
    mtval: ReadWriteRiscvCsr::new(),
    mtval2: ReadWriteRiscvCsr::new(),
    mtvec: ReadWriteRiscvCsr::new(),
    mscratch: ReadWriteRiscvCsr::new(),
    mhartid: ReadWriteRiscvCsr::new(),
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
    // PMP
    pmpcfg0: ReadWriteRiscvCsr::new(),
    pmpaddr0: ReadWriteRiscvCsr::new(),
    pmpaddr1: ReadWriteRiscvCsr::new(),
};

#[derive(Copy, Clone)]
pub struct ReadWriteRiscvCsr<const V: u16> {}

impl<const V: u16> ReadWriteRiscvCsr<V> {
    pub const fn new() -> Self {
        ReadWriteRiscvCsr {}
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
