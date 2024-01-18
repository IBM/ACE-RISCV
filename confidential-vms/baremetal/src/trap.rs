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
        TrapFrame {
            regs: [0; 32],
            trap_stack: null_mut(),
        }
    }
}

#[no_mangle]
extern "C" fn trap_handler(
    sepc: usize,
    stval: usize,
    scause: usize,
) -> usize {
    let is_async = (scause >> 63 & 1) == 1;
    let cause_num = scause & 0xfff;
    let mut return_pc = sepc;
    if is_async {
        // println!("Supervisor software interrupt!");
        // match cause_num {
            // _ => panic!("Unhandled interrupt -> {}\n", cause_num),
        // }
    } else {
        // match cause_num {
        //     2 => {
        //         // println!("Illegal instruction at 0x{:08x}: 0x{:08x}", epc, tval);
        //         return_pc += 4;
        //     }
        //     5 => {
        //         // println!("Illegal memory access from 0x{:08x}: 0x{:08x}", epc, tval);
        //         return_pc += 4;
        //     }
        //     7 => {
        //         // println!("Illegal memory access from 0x{:08x}: 0x{:08x}", epc, tval);
        //         return_pc += 4;
        //     }
        //     _ => panic!("Unhandled trap -> {}\n", cause_num),
        // }
        return_pc += 4;
    };
    return_pc
}
