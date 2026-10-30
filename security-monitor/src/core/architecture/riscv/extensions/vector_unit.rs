// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::specification::{CSR_VCSR, CSR_VL, CSR_VLENB, CSR_VSTART, CSR_VTYPE, SR_VS_DIRTY};
use crate::core::architecture::{CSR, HardwareExtension};
use crate::core::hardware_setup::HardwareSetup;
use alloc::vec;
use alloc::vec::Vec;
use core::arch::asm;

const NUMBER_OF_VECTOR_REGISTERS: usize = 32;

#[repr(C)]
pub struct VectorUnit {
    registers: Vec<u8>,
    vlenb: usize,
    vl: usize,
    vtype: usize,
    vstart: usize,
    vcsr: usize,
}

impl VectorUnit {
    pub fn empty() -> Self {
        debug!("ACE_DIAG: Enter VectorUnit::empty");

        let sp: usize;

        unsafe {
            asm!(
                "mv {value}, sp",
                value = out(reg) sp,
                options(nomem, nostack)
            );
        }

        debug!("ACE_DIAG: VectorUnit::empty ENTRY sp={:#x} initialized={}", sp, HardwareSetup::is_initialized());

        let vector_supported = HardwareSetup::is_extension_supported(HardwareExtension::VectorExtension);

        debug!("ACE_DIAG: VectorUnit supported = {}", vector_supported);

        if !vector_supported {
            return Self { registers: Vec::new(), vlenb: 0, vl: 0, vtype: 0, vstart: 0, vcsr: 0 };
        }

        debug!("ACE_DIAG: BEFORE mstatus/CSR, initialized={}", HardwareSetup::is_initialized());

        let old_mstatus = CSR.mstatus.read_and_set_bits(SR_VS_DIRTY);

        let vlenb: usize;
        unsafe {
            asm!(
                "csrr {value}, {csr}",
                value = out(reg) vlenb,
                csr = const CSR_VLENB
            );
        }

        CSR.mstatus.write(old_mstatus);

        debug!("ACE_DIAG: AFTER mstatus/CSR, initialized={}, vlenb={}", HardwareSetup::is_initialized(), vlenb);

        assert!(vlenb > 0);

        let length = NUMBER_OF_VECTOR_REGISTERS.checked_mul(vlenb).expect("Invalid vector register size");

        debug!("ACE_DIAG: BEFORE vector allocation, initialized={}, length={}", HardwareSetup::is_initialized(), length);

        let registers = vec![0; length];

        debug!("ACE_DIAG: AFTER vector allocation, initialized={}, ptr={:p}", HardwareSetup::is_initialized(), registers.as_ptr());

        debug!("ACE_DIAG: Leaving VectorUnit::empty");

        Self { registers, vlenb, vl: 0, vtype: 0, vstart: 0, vcsr: 0 }
    }

    unsafe fn validate_vlenb(&self) {
        let mut vlenb: usize;
        unsafe { asm!("csrr {value}, {csr}", value = out(reg) vlenb, csr = const CSR_VLENB) };
        assert_eq!(self.vlenb, vlenb);
        assert_eq!(self.registers.len(), NUMBER_OF_VECTOR_REGISTERS * vlenb);
    }

    pub unsafe fn save_in_main_memory(&mut self) {
        unsafe { self.validate_vlenb() };
        unsafe {
            asm!("csrr {value}, {csr}", value = out(reg) self.vl, csr = const CSR_VL);
            asm!("csrr {value}, {csr}", value = out(reg) self.vtype, csr = const CSR_VTYPE);
            asm!("csrr {value}, {csr}", value = out(reg) self.vstart, csr = const CSR_VSTART);
            asm!("csrr {value}, {csr}", value = out(reg) self.vcsr, csr = const CSR_VCSR);
            asm!("csrw {csr}, zero", csr = const CSR_VSTART);
        }

        macro_rules! store {
            ($index:literal) => {
                unsafe {
                    asm!(
                        ".option push",
                        ".option arch, +v",
                        concat!("vs1r.v v", stringify!($index), ", ({address})"),
                        ".option pop",
                        address = in(reg) self.registers.as_mut_ptr().add($index * self.vlenb)
                    );
                }
            };
        }

        store!(0);
        store!(1);
        store!(2);
        store!(3);
        store!(4);
        store!(5);
        store!(6);
        store!(7);
        store!(8);
        store!(9);
        store!(10);
        store!(11);
        store!(12);
        store!(13);
        store!(14);
        store!(15);
        store!(16);
        store!(17);
        store!(18);
        store!(19);
        store!(20);
        store!(21);
        store!(22);
        store!(23);
        store!(24);
        store!(25);
        store!(26);
        store!(27);
        store!(28);
        store!(29);
        store!(30);
        store!(31);
    }

    pub unsafe fn restore_from_main_memory(&self) {
        unsafe { self.validate_vlenb() };
        unsafe { asm!("csrw {csr}, zero", csr = const CSR_VSTART) };

        macro_rules! load {
            ($index:literal) => {
                unsafe {
                    asm!(
                        ".option push",
                        ".option arch, +v",
                        concat!("vl1re8.v v", stringify!($index), ", ({address})"),
                        ".option pop",
                        address = in(reg) self.registers.as_ptr().add($index * self.vlenb)
                    );
                }
            };
        }

        load!(0);
        load!(1);
        load!(2);
        load!(3);
        load!(4);
        load!(5);
        load!(6);
        load!(7);
        load!(8);
        load!(9);
        load!(10);
        load!(11);
        load!(12);
        load!(13);
        load!(14);
        load!(15);
        load!(16);
        load!(17);
        load!(18);
        load!(19);
        load!(20);
        load!(21);
        load!(22);
        load!(23);
        load!(24);
        load!(25);
        load!(26);
        load!(27);
        load!(28);
        load!(29);
        load!(30);
        load!(31);
        unsafe {
            asm!(
                ".option push",
                ".option arch, +v",
                "vsetvl zero, {saved_vl}, {saved_vtype}",
                ".option pop",
                saved_vl = in(reg) self.vl,
                saved_vtype = in(reg) self.vtype
            );
            asm!("csrw {csr}, {value}", csr = const CSR_VCSR, value = in(reg) self.vcsr);
            asm!("csrw {csr}, {value}", csr = const CSR_VSTART, value = in(reg) self.vstart);
        }
    }
}
