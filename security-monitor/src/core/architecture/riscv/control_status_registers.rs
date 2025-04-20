// SPDX-FileCopyrightText: 2023 Rivos Inc.
// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
// This implementation is based on the code from Rivos. We just use a subset of functionalities and CSRs because we do not need all of them.
// https://github.com/rivosinc/salus/blob/fd06d5959fd81c02b8763c1922f36cc0ebe7d301/riscv-regs/src/csrs/csr_access.rs#L47
#![allow(unused)]
use super::specification::*;
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::control_data::{DigestType, MeasurementDigest};
use core::arch::asm;

/// Represents all control status registers (CSRs) accessible to modes less privileged than M-mode.
#[repr(C)]
pub struct ControlStatusRegisters {
    pub mepc: ReadWriteRiscvCsr<CSR_MEPC>,
    pub mstatus: ReadWriteRiscvCsr<CSR_MSTATUS>,
    // Safety: Architectural hart state must be bitwise equal to corresponding OpenSBI structure.
    //         For that reason, this structure is layouted according to C convention and it starts
    //         with mepc and mstatus. When updating to new version of OpenSBI, make sure that
    //         CSRs' order in this structure is correct.
    pub mcause: ReadWriteRiscvCsr<CSR_MCAUSE>,
    pub medeleg: ReadWriteRiscvCsr<CSR_MEDELEG>,
    pub mideleg: ReadWriteRiscvCsr<CSR_MIDELEG>,
    pub mie: ReadWriteRiscvCsr<CSR_MIE>,
    pub mip: ReadRiscvCsr<CSR_MIP>,
    pub mtinst: ReadWriteRiscvCsr<CSR_MTINST>,
    pub mtval: ReadWriteRiscvCsr<CSR_MTVAL>,
    pub mtval2: ReadWriteRiscvCsr<CSR_MTVAL2>,
    pub mtvec: ReadWriteRiscvCsr<CSR_MTVEC>,
    pub mscratch: ReadWriteRiscvCsr<CSR_MSCRATCH>,
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
    // S-mode Debug extension should never be present due to security concerns
    pub scontext: ReadWriteRiscvCsr<CSR_SCONTEXT>,
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
}

impl ControlStatusRegisters {
    pub fn empty() -> Self {
        let mut csrs = Self {
            mepc: ReadWriteRiscvCsr::new(),
            mstatus: ReadWriteRiscvCsr::new(),
            mcause: ReadWriteRiscvCsr::new(),
            medeleg: ReadWriteRiscvCsr::new(),
            mideleg: ReadWriteRiscvCsr::new(),
            mie: ReadWriteRiscvCsr::new(),
            mip: ReadRiscvCsr::new(),
            mtinst: ReadWriteRiscvCsr::new(),
            mtval: ReadWriteRiscvCsr::new(),
            mtval2: ReadWriteRiscvCsr::new(),
            mtvec: ReadWriteRiscvCsr::new(),
            mscratch: ReadWriteRiscvCsr::new(),
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
        };
        csrs
    }

    pub fn save_in_main_memory(&mut self) {
        self.mepc.save_in_main_memory();
        self.mstatus.save_in_main_memory();
        self.mcause.save_in_main_memory();
        self.medeleg.save_in_main_memory();
        self.mideleg.save_in_main_memory();
        self.mie.save_in_main_memory();
        self.mtinst.save_in_main_memory();
        self.mtval.save_in_main_memory();
        self.mtval2.save_in_main_memory();
        self.mtvec.save_in_main_memory();
        self.mscratch.save_in_main_memory();
        // S-mode
        self.sstatus.save_in_main_memory();
        self.sie.save_in_main_memory();
        self.stvec.save_in_main_memory();
        self.scounteren.save_in_main_memory();
        self.senvcfg.save_in_main_memory();
        self.sscratch.save_in_main_memory();
        self.sepc.save_in_main_memory();
        self.scause.save_in_main_memory();
        self.stval.save_in_main_memory();
        self.sip.save_in_main_memory();
        self.satp.save_in_main_memory();
        // DEBUG extension should never be present due to security concerns.
        // self.scontext.save_in_main_memory();
        // HS-mode
        self.hstatus.save_in_main_memory();
        self.hedeleg.save_in_main_memory();
        self.hideleg.save_in_main_memory();
        self.hie.save_in_main_memory();
        self.hcounteren.save_in_main_memory();
        self.hgeie.save_in_main_memory();
        self.htval.save_in_main_memory();
        self.hip.save_in_main_memory();
        self.hvip.save_value_in_main_memory(self.hvip.read() & !MIE_VSTIP_MASK);
        self.htinst.save_in_main_memory();
        self.hgeip.save_in_main_memory();
        self.henvcfg.save_in_main_memory();
        self.hgatp.save_in_main_memory();
        // DEBUG extension should never be present due to security concerns.
        // self.hcontext.save_in_main_memory();
        self.htimedelta.save_in_main_memory();
        // VS-mode
        self.vsstatus.save_in_main_memory();
        self.vsie.save_in_main_memory();
        self.vsip.save_in_main_memory();
        self.vstvec.save_in_main_memory();
        self.vsscratch.save_in_main_memory();
        self.vsepc.save_in_main_memory();
        self.vscause.save_in_main_memory();
        self.vstval.save_in_main_memory();
        self.vsatp.save_in_main_memory();
    }

    pub fn restore_from_main_memory(&self) {
        self.mepc.restore_from_main_memory();
        self.mstatus.restore_from_main_memory();
        self.mcause.restore_from_main_memory();
        self.medeleg.restore_from_main_memory();
        self.mideleg.restore_from_main_memory();
        self.mie.restore_from_main_memory();
        self.mtinst.restore_from_main_memory();
        self.mtval.restore_from_main_memory();
        self.mtval2.restore_from_main_memory();
        self.mtvec.restore_from_main_memory();
        // S-mode
        self.sstatus.restore_from_main_memory();
        self.sie.restore_from_main_memory();
        self.stvec.restore_from_main_memory();
        self.scounteren.restore_from_main_memory();
        self.senvcfg.restore_from_main_memory();
        self.sscratch.restore_from_main_memory();
        self.sepc.restore_from_main_memory();
        self.scause.restore_from_main_memory();
        self.stval.restore_from_main_memory();
        self.sip.restore_from_main_memory();
        self.satp.restore_from_main_memory();
        // DEBUG extension should never be present due to security concerns.
        // self.scontext.restore_from_main_memory();
        // HS-mode
        self.hstatus.restore_from_main_memory();
        self.hedeleg.restore_from_main_memory();
        self.hideleg.restore_from_main_memory();
        self.hie.restore_from_main_memory();
        self.hcounteren.restore_from_main_memory();
        self.hgeie.restore_from_main_memory();
        self.htval.restore_from_main_memory();
        // self.hip.restore_from_main_memory();
        self.hvip.restore_from_main_memory();
        self.htinst.restore_from_main_memory();
        // self.hgeip.restore_from_main_memory();
        self.henvcfg.restore_from_main_memory();
        self.hgatp.restore_from_main_memory();
        // DEBUG extension should never be present due to security concerns.
        // self.hcontext.restore_from_main_memory();
        self.htimedelta.restore_from_main_memory();
        // VS-mode
        self.vsstatus.restore_from_main_memory();
        self.vsie.restore_from_main_memory();
        self.vsip.restore_from_main_memory();
        self.vstvec.restore_from_main_memory();
        self.vsscratch.restore_from_main_memory();
        self.vsepc.restore_from_main_memory();
        self.vscause.restore_from_main_memory();
        self.vstval.restore_from_main_memory();
        self.vsatp.restore_from_main_memory();
    }

    /// Extends the measurement digest with the context of all CSRs.
    pub fn measure(&self, digest: &mut MeasurementDigest) {
        use sha2::Digest;
        let mut hasher = DigestType::new_with_prefix(digest.clone());
        hasher.update(self.mepc.read_from_main_memory().to_le_bytes());
        hasher.update(self.mcause.read_from_main_memory().to_le_bytes());
        hasher.update(self.medeleg.read_from_main_memory().to_le_bytes());
        hasher.update(self.mideleg.read_from_main_memory().to_le_bytes());
        hasher.update(self.mie.read_from_main_memory().to_le_bytes());
        hasher.update(self.mstatus.read_from_main_memory().to_le_bytes());
        hasher.update(self.mtinst.read_from_main_memory().to_le_bytes());
        hasher.update(self.mtval.read_from_main_memory().to_le_bytes());
        hasher.update(self.mtval2.read_from_main_memory().to_le_bytes());
        hasher.update(self.mtvec.read_from_main_memory().to_le_bytes());
        // S-mode
        hasher.update(self.sstatus.read_from_main_memory().to_le_bytes());
        hasher.update(self.sie.read_from_main_memory().to_le_bytes());
        hasher.update(self.stvec.read_from_main_memory().to_le_bytes());
        hasher.update(self.scounteren.read_from_main_memory().to_le_bytes());
        hasher.update(self.senvcfg.read_from_main_memory().to_le_bytes());
        hasher.update(self.sscratch.read_from_main_memory().to_le_bytes());
        hasher.update(self.sepc.read_from_main_memory().to_le_bytes());
        hasher.update(self.scause.read_from_main_memory().to_le_bytes());
        hasher.update(self.stval.read_from_main_memory().to_le_bytes());
        hasher.update(self.sip.read_from_main_memory().to_le_bytes());
        hasher.update(self.satp.read_from_main_memory().to_le_bytes());
        hasher.update(self.scontext.read_from_main_memory().to_le_bytes());
        // HS-mode
        hasher.update(self.hstatus.read_from_main_memory().to_le_bytes());
        hasher.update(self.hedeleg.read_from_main_memory().to_le_bytes());
        hasher.update(self.hideleg.read_from_main_memory().to_le_bytes());
        hasher.update(self.hie.read_from_main_memory().to_le_bytes());
        hasher.update(self.hcounteren.read_from_main_memory().to_le_bytes());
        hasher.update(self.hgeie.read_from_main_memory().to_le_bytes());
        hasher.update(self.htval.read_from_main_memory().to_le_bytes());
        hasher.update(self.hip.read_from_main_memory().to_le_bytes());
        hasher.update(self.hvip.read_from_main_memory().to_le_bytes());
        hasher.update(self.htinst.read_from_main_memory().to_le_bytes());
        hasher.update(self.hgeip.read_from_main_memory().to_le_bytes());
        hasher.update(self.henvcfg.read_from_main_memory().to_le_bytes());
        hasher.update(self.hgatp.read_from_main_memory().to_le_bytes());
        hasher.update(self.hcontext.read_from_main_memory().to_le_bytes());
        hasher.update(self.htimedelta.read_from_main_memory().to_le_bytes());
        // VS-mode
        hasher.update(self.vsstatus.read_from_main_memory().to_le_bytes());
        hasher.update(self.vsie.read_from_main_memory().to_le_bytes());
        hasher.update(self.vsip.read_from_main_memory().to_le_bytes());
        hasher.update(self.vstvec.read_from_main_memory().to_le_bytes());
        hasher.update(self.vsscratch.read_from_main_memory().to_le_bytes());
        hasher.update(self.vsepc.read_from_main_memory().to_le_bytes());
        hasher.update(self.vscause.read_from_main_memory().to_le_bytes());
        hasher.update(self.vstval.read_from_main_memory().to_le_bytes());
        hasher.update(self.vsatp.read_from_main_memory().to_le_bytes());
        hasher.finalize_into(digest);
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

    pub const fn new_with_value(value: usize) -> Self {
        ReadWriteRiscvCsr(value)
    }

    pub fn save_in_main_memory(&mut self) {
        self.0 = self.read();
    }

    pub fn save_value_in_main_memory(&mut self, value: usize) {
        self.0 = value;
    }

    pub fn save_nacl_value_in_main_memory(&mut self, nacl_shared_memory: &NaclSharedMemory) {
        self.0 = nacl_shared_memory.csr(V.into());
    }

    pub fn restore_from_main_memory(&self) {
        self.write(self.0);
    }

    pub fn read_from_main_memory(&self) -> usize {
        self.0
    }

    pub fn add(&mut self, value: usize) {
        self.0 = self.0 + value;
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
    pub fn write(&self, val_to_set: usize) {
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
