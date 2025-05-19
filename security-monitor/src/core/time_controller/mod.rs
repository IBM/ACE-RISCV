// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub struct TimeController {}

impl TimeController {
    const TIME_MMIO_ADDRESS: usize = 0x200BFF8;

    pub fn read_time() -> usize {
        unsafe { (Self::TIME_MMIO_ADDRESS as *const usize).read_volatile() }
    }
}
