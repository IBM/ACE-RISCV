// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use core::convert::TryInto;
use core::fmt::{Error, Write};

pub struct Uart {
    base_address: usize,
}

impl Write for Uart {
    fn write_str(&mut self, out: &str) -> Result<(), Error> {
        for c in out.bytes() {
            self.put(c);
        }
        Ok(())
    }
}

impl Uart {
    pub fn new(base_address: usize) -> Self {
        let uart = Uart { base_address };
        let ptr = uart.base_address as *mut u8;
        unsafe {
            ptr.add(3).write_volatile((1 << 0) | (1 << 1));
            ptr.add(2).write_volatile(1 << 0);
            ptr.add(1).write_volatile(1 << 0);
            let divisor: u16 = 592;
            let divisor_least: u8 = (divisor & 0xff).try_into().unwrap();
            let divisor_most: u8 = (divisor >> 8).try_into().unwrap();
            let lcr = ptr.add(3).read_volatile();
            ptr.add(3).write_volatile(lcr | 1 << 7);
            ptr.add(0).write_volatile(divisor_least);
            ptr.add(1).write_volatile(divisor_most);
            ptr.add(3).write_volatile(lcr);
        }
        uart
    }

    pub fn put(&mut self, c: u8) {
        let ptr = self.base_address as *mut u8;
        unsafe {
            ptr.add(0).write_volatile(c);
        }
    }

    pub fn println(&mut self, out: &str) {
        crate::sync::acquire(crate::sync::UART_SYNC_ADDRESS);
        for c in out.bytes() {
            self.put(c);
        }
        self.put('\n' as u8);
        crate::sync::release(crate::sync::UART_SYNC_ADDRESS);
    }
}
