// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

use crate::core::architecture::riscv::control_status_registers::ReadWriteRiscvCsr;
use crate::core::architecture::riscv::specification::{CSR_VCSR, CSR_VL, CSR_VSTART, CSR_VTYPE};
use crate::core::hardware_setup::HardwareSetup;
use crate::error::Error;
use alloc::vec::Vec;
use core::arch::asm;

const NUMBER_OF_VECTOR_REGISTERS: usize = 32;

#[repr(C)]
pub struct VectorUnit {
    registers: Vec<u8>,
    vlenb: usize,
    vl: ReadWriteRiscvCsr<CSR_VL>,
    vtype: ReadWriteRiscvCsr<CSR_VTYPE>,
    vstart: ReadWriteRiscvCsr<CSR_VSTART>,
    vcsr: ReadWriteRiscvCsr<CSR_VCSR>,
}

impl VectorUnit {
    pub fn empty() -> Result<Self, Error> {
        let vlenb = HardwareSetup::vector_vlenb()?;

        let length = NUMBER_OF_VECTOR_REGISTERS.checked_mul(vlenb).ok_or(Error::InvalidVectorRegisterSize())?;

        let mut registers = Vec::new();
        registers.try_reserve_exact(length).map_err(|_| Error::NotEnoughMemory())?;
        registers.resize(length, 0);

        Ok(Self {
            registers,
            vlenb,
            vl: ReadWriteRiscvCsr::new(),
            vtype: ReadWriteRiscvCsr::new(),
            vstart: ReadWriteRiscvCsr::new(),
            vcsr: ReadWriteRiscvCsr::new(),
        })
    }

    /// Saves vector state in main memory.
    ///
    /// # Safety
    ///
    /// The vector extension must be supported and enabled.
    pub unsafe fn save_in_main_memory(&mut self) {
        self.vl.save_in_main_memory();
        self.vtype.save_in_main_memory();
        self.vstart.save_in_main_memory();
        self.vcsr.save_in_main_memory();

        self.vstart.write(0);

        macro_rules! store {
            ($index:literal) => {
                unsafe {
                    asm!(
                        ".option push",
                        ".option arch, +v",
                        concat!(
                            "vs8r.v v",
                            stringify!($index),
                            ", ({address})"
                        ),
                        ".option pop",
                        address = in(reg) self.registers
                            .as_mut_ptr()
                            .add($index * self.vlenb),
                    );
                }
            };
        }

        store!(0);
        store!(8);
        store!(16);
        store!(24);
    }

    /// Restores vector state from main memory.
    ///
    /// # Safety
    ///
    /// The vector extension must be supported and enabled.
    /// The current hart must have a compatible vector configuration.
    pub unsafe fn restore_from_main_memory(&self) {
        self.vstart.write(0);

        macro_rules! load {
            ($index:literal) => {
                unsafe {
                    asm!(
                        ".option push",
                        ".option arch, +v",
                        concat!(
                            "vl8re8.v v",
                            stringify!($index),
                            ", ({address})"
                        ),
                        ".option pop",
                        address = in(reg) self.registers
                            .as_ptr()
                            .add($index * self.vlenb),
                    );
                }
            };
        }

        load!(0);
        load!(8);
        load!(16);
        load!(24);

        unsafe {
            asm!(
                ".option push",
                ".option arch, +v",
                "vsetvl zero, {saved_vl}, {saved_vtype}",
                ".option pop",
                saved_vl = in(reg) self.vl.read_from_main_memory(),
                saved_vtype = in(reg) self.vtype.read_from_main_memory(),
            );
        }

        self.vcsr.restore_from_main_memory();
        self.vstart.restore_from_main_memory();
    }
}
