// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use core::ptr::null_mut;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct TrapFrame {
    pub regs: [usize; 32],
    pub trap_stack: *mut u8,
}

impl TrapFrame {
    pub const fn zero() -> Self {
        TrapFrame { regs: [0; 32], trap_stack: null_mut() }
    }
}

#[no_mangle]
extern "C" fn trap_handler(sepc: usize, _stval: usize, scause: usize) -> usize {
    let is_async = (scause >> 63 & 1) == 1;
    // let cause_num = scause & 0xfff;
    let mut return_pc = sepc;
    if is_async {
    } else {
        return_pc += 4;
    };
    return_pc
}
