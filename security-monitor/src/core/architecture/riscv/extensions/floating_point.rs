// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

macro_rules! fasm {
    ($op:tt, $token:expr, $mem:expr) =>  {
        core::arch::asm!(concat!($op, " f", stringify!($token), ", 0({val})"), val = in(reg) core::ptr::addr_of!($mem[$token]) as usize);
    }
}

#[repr(C)]
pub struct FloatingPointRegisters(pub [usize; Self::LEN]);

impl FloatingPointRegisters {
    const LEN: usize = 32;

    pub fn empty() -> Self {
        Self([0; Self::LEN])
    }

    pub fn save_in_main_memory(&mut self) {
        unsafe {
            fasm!("fld", 0, self.0);
            fasm!("fld", 1, self.0);
            fasm!("fld", 2, self.0);
            fasm!("fld", 3, self.0);
            fasm!("fld", 4, self.0);
            fasm!("fld", 5, self.0);
            fasm!("fld", 6, self.0);
            fasm!("fld", 7, self.0);
            fasm!("fld", 8, self.0);
            fasm!("fld", 9, self.0);
            fasm!("fld", 10, self.0);
            fasm!("fld", 11, self.0);
            fasm!("fld", 12, self.0);
            fasm!("fld", 13, self.0);
            fasm!("fld", 14, self.0);
            fasm!("fld", 15, self.0);
            fasm!("fld", 16, self.0);
            fasm!("fld", 17, self.0);
            fasm!("fld", 18, self.0);
            fasm!("fld", 19, self.0);
            fasm!("fld", 20, self.0);
            fasm!("fld", 21, self.0);
            fasm!("fld", 22, self.0);
            fasm!("fld", 23, self.0);
            fasm!("fld", 24, self.0);
            fasm!("fld", 25, self.0);
            fasm!("fld", 26, self.0);
            fasm!("fld", 27, self.0);
            fasm!("fld", 28, self.0);
            fasm!("fld", 29, self.0);
            fasm!("fld", 30, self.0);
            fasm!("fld", 31, self.0);
        }
    }

    pub fn restore_from_main_memory(&mut self) {
        unsafe {
            fasm!("fsd", 0, self.0);
            fasm!("fsd", 1, self.0);
            fasm!("fsd", 2, self.0);
            fasm!("fsd", 3, self.0);
            fasm!("fsd", 4, self.0);
            fasm!("fsd", 5, self.0);
            fasm!("fsd", 6, self.0);
            fasm!("fsd", 7, self.0);
            fasm!("fsd", 8, self.0);
            fasm!("fsd", 9, self.0);
            fasm!("fsd", 10, self.0);
            fasm!("fsd", 11, self.0);
            fasm!("fsd", 12, self.0);
            fasm!("fsd", 13, self.0);
            fasm!("fsd", 14, self.0);
            fasm!("fsd", 15, self.0);
            fasm!("fsd", 16, self.0);
            fasm!("fsd", 17, self.0);
            fasm!("fsd", 18, self.0);
            fasm!("fsd", 19, self.0);
            fasm!("fsd", 20, self.0);
            fasm!("fsd", 21, self.0);
            fasm!("fsd", 22, self.0);
            fasm!("fsd", 23, self.0);
            fasm!("fsd", 24, self.0);
            fasm!("fsd", 25, self.0);
            fasm!("fsd", 26, self.0);
            fasm!("fsd", 27, self.0);
            fasm!("fsd", 28, self.0);
            fasm!("fsd", 29, self.0);
            fasm!("fsd", 30, self.0);
            fasm!("fsd", 31, self.0);
        }
    }
}
