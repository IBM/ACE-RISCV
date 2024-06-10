// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::control_status_registers::ReadWriteRiscvCsr;
use crate::core::architecture::specification::{CSR_FCSR, CSR_FFLAGS, CSR_FRM, SR_FS, SR_FS_CLEAN, SR_FS_DIRTY};

macro_rules! fasm {
    ($op:tt, $token:expr, $mem:expr) =>  {
        core::arch::asm!(concat!($op, " f", stringify!($token), ", 0({val})"), val = in(reg) core::ptr::addr_of!($mem[$token]) as usize);
    }
}

#[repr(C)]
pub struct FloatingPointUnit {
    fflags: ReadWriteRiscvCsr<CSR_FFLAGS>,
    frm: ReadWriteRiscvCsr<CSR_FRM>,
    fcsr: ReadWriteRiscvCsr<CSR_FCSR>,
    registers: [usize; Self::LEN],
}

impl FloatingPointUnit {
    const LEN: usize = 32;

    pub fn empty() -> Self {
        Self { fflags: ReadWriteRiscvCsr::new(), frm: ReadWriteRiscvCsr::new(), fcsr: ReadWriteRiscvCsr::new(), registers: [0; Self::LEN] }
    }

    /// Saves in main memory the float point unit state.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the FPU hardware exists and is enabled.
    pub unsafe fn save_in_main_memory(&mut self) {
        self.fflags.save_in_main_memory();
        self.frm.save_in_main_memory();
        self.fcsr.save_in_main_memory();

        unsafe {
            fasm!("fld", 0, self.registers);
            fasm!("fld", 1, self.registers);
            fasm!("fld", 2, self.registers);
            fasm!("fld", 3, self.registers);
            fasm!("fld", 4, self.registers);
            fasm!("fld", 5, self.registers);
            fasm!("fld", 6, self.registers);
            fasm!("fld", 7, self.registers);
            fasm!("fld", 8, self.registers);
            fasm!("fld", 9, self.registers);
            fasm!("fld", 10, self.registers);
            fasm!("fld", 11, self.registers);
            fasm!("fld", 12, self.registers);
            fasm!("fld", 13, self.registers);
            fasm!("fld", 14, self.registers);
            fasm!("fld", 15, self.registers);
            fasm!("fld", 16, self.registers);
            fasm!("fld", 17, self.registers);
            fasm!("fld", 18, self.registers);
            fasm!("fld", 19, self.registers);
            fasm!("fld", 20, self.registers);
            fasm!("fld", 21, self.registers);
            fasm!("fld", 22, self.registers);
            fasm!("fld", 23, self.registers);
            fasm!("fld", 24, self.registers);
            fasm!("fld", 25, self.registers);
            fasm!("fld", 26, self.registers);
            fasm!("fld", 27, self.registers);
            fasm!("fld", 28, self.registers);
            fasm!("fld", 29, self.registers);
            fasm!("fld", 30, self.registers);
            fasm!("fld", 31, self.registers);
        }
    }

    /// Restores from main memory the float point unit state.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the FPU hardware exists and is enabled.
    pub unsafe fn restore_from_main_memory(&mut self) {
        self.fflags.restore_from_main_memory();
        self.frm.restore_from_main_memory();
        self.fcsr.restore_from_main_memory();

        unsafe {
            fasm!("fsd", 0, self.registers);
            fasm!("fsd", 1, self.registers);
            fasm!("fsd", 2, self.registers);
            fasm!("fsd", 3, self.registers);
            fasm!("fsd", 4, self.registers);
            fasm!("fsd", 5, self.registers);
            fasm!("fsd", 6, self.registers);
            fasm!("fsd", 7, self.registers);
            fasm!("fsd", 8, self.registers);
            fasm!("fsd", 9, self.registers);
            fasm!("fsd", 10, self.registers);
            fasm!("fsd", 11, self.registers);
            fasm!("fsd", 12, self.registers);
            fasm!("fsd", 13, self.registers);
            fasm!("fsd", 14, self.registers);
            fasm!("fsd", 15, self.registers);
            fasm!("fsd", 16, self.registers);
            fasm!("fsd", 17, self.registers);
            fasm!("fsd", 18, self.registers);
            fasm!("fsd", 19, self.registers);
            fasm!("fsd", 20, self.registers);
            fasm!("fsd", 21, self.registers);
            fasm!("fsd", 22, self.registers);
            fasm!("fsd", 23, self.registers);
            fasm!("fsd", 24, self.registers);
            fasm!("fsd", 25, self.registers);
            fasm!("fsd", 26, self.registers);
            fasm!("fsd", 27, self.registers);
            fasm!("fsd", 28, self.registers);
            fasm!("fsd", 29, self.registers);
            fasm!("fsd", 30, self.registers);
            fasm!("fsd", 31, self.registers);
        }
    }
}
