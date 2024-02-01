// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#[derive(Debug)]
pub struct OpensbiResult {
    pub trap_regs: opensbi_sys::sbi_trap_regs,
    pub vsstatus: usize,
    pub vstval: usize,
    pub vsepc: usize,
    pub vscause: usize,
    pub hstatus: usize,
    pub htval: usize,
    pub htinst: usize,
    pub stval: usize,
    pub sepc: usize,
    pub scause: usize,
}

impl OpensbiResult {
    pub fn from_opensbi_handler(trap_regs: opensbi_sys::sbi_trap_regs) -> Self {
        // As a temporal solution we hardcode a bunch of CSRs and read them via assembly. The final solution should rely on existing crate
        // giving access to these CSRs (e.g., riscv or riscv-regs) or a custom solution with CSRs generated from RISC-V spec.
        Self {
            trap_regs,
            vsstatus: read_vsstatus(),
            vstval: read_vstval(),
            vsepc: read_vsepc(),
            vscause: read_vscause(),
            hstatus: read_hstatus(),
            htval: read_htval(),
            htinst: read_htinst(),
            stval: read_stval(),
            sepc: read_sepc(),
            scause: read_scause(),
        }
    }
}

fn read_vsstatus() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x200, x0"), out(reg) r);
    }
    r
}

fn read_vstval() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x243, x0"), out(reg) r);
    }
    r
}

fn read_vsepc() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x241, x0"), out(reg) r);
    }
    r
}

fn read_vscause() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x242, x0"), out(reg) r);
    }
    r
}

fn read_hstatus() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x600, x0"), out(reg) r);
    }
    r
}

fn read_htval() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x643, x0"), out(reg) r);
    }
    r
}

fn read_htinst() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x64a, x0"), out(reg) r);
    }
    r
}

fn read_stval() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x143, x0"), out(reg) r);
    }
    r
}

fn read_sepc() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x141, x0"), out(reg) r);
    }
    r
}

fn read_scause() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x142, x0"), out(reg) r);
    }
    r
}
