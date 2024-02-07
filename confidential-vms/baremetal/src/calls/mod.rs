// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#[warn(unused_assignments)]
use core::arch::asm;

pub mod ace;
pub mod sm;

fn ecall(extid: usize, fid: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> Result<usize, usize> {
    let (mut error, mut value);
    unsafe {
        asm!("ecall", in("a0") a0, in("a1") a1, in("a2") a2, in("a3") a3, in("a4") a4, in("a6") fid, in("a7") extid, lateout("a0") error, lateout("a1") value)
    };
    if error > 0 {
        Err(error)
    } else {
        Ok(value)
    }
}
