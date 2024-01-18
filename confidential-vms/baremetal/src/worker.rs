// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::Uart;
use crate::UART_BASE_ADDRESS;
use crate::trap_handler_asm;
use crate::trap;
use crate::format;

#[no_mangle]
extern "C" fn worker_init(hart_id: usize) {
    let mut uart = Uart::new(UART_BASE_ADDRESS);
    uart.println(&format!("Hello from hart id: {}", hart_id));

    let trap_handler_asm_address: usize = (trap_handler_asm as usize).try_into().unwrap();
    uart.println(&format!("trap handler address: {:x}", trap_handler_asm_address));

    unsafe {
        // set the address of the trap handler 
        riscv::register::stvec::write(trap_handler_asm_address, riscv::register::mtvec::TrapMode::Direct);
        // store the address of the trap frame
        let trap_frame_address: usize = (&mut crate::TRAP_FRAME[hart_id][0] as *mut trap::TrapFrame) as usize;
        riscv::register::sscratch::write(trap_frame_address);
        // enable interrupts
        riscv::register::sie::set_ssoft();
        riscv::register::sie::clear_stimer();
        riscv::register::sie::clear_sext();
        riscv::register::sstatus::set_sie();
    }

    sbi::system_reset::system_reset(
        sbi::system_reset::ResetType::Shutdown,
        sbi::system_reset::ResetReason::NoReason,
    )
    .expect("system reset failed");
} 
