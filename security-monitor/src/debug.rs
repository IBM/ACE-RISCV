// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
use crate::core::architecture::CSR;
use core::convert::TryInto;
use core::fmt::{Error, Write};

#[macro_export]
macro_rules! assure {
    ($cond:expr, $error:expr) => {
        if !$cond {
            Err($error)
        } else {
            Ok(())
        }
    };
}

#[macro_export]
macro_rules! assure_not {
    ($cond:expr, $error:expr) => {
        if $cond {
            Err($error)
        } else {
            Ok(())
        }
    };
}

#[cfg(feature = "verbose")]
pub fn __printout_metadata(svm_id: usize) {}

#[cfg(feature = "verbose")]
pub fn __print_pmp_configuration() {
    use crate::core::architecture::PMP_ADDRESS_SHIFT;
    let pmpcfg0 = CSR.pmpcfg0.read();
    let pmp0 = CSR.pmpaddr0.read();
    let pmp0cfg = pmpcfg0 & 0b11111111;
    debug!("pmp0 value: {:x}, shifted {:x}", pmp0, pmp0 << PMP_ADDRESS_SHIFT);
    debug!("pmp0 cfg: {:?}", pmp0cfg);

    let pmp1 = CSR.pmpaddr1.read();
    let pmp1cfg = pmpcfg0 & 0b1111111100000000;
    debug!("pmp1 value: {:x}, shifted {:x}", pmp1, pmp1 << PMP_ADDRESS_SHIFT);
    debug!("pmp1 cfg: {:?}", pmp1cfg);
}

#[cfg(feature = "verbose")]
fn read_memory(address: usize) -> u64 {
    let ptr = (address) as *mut u64;
    unsafe { ptr.read_volatile() }
}

#[cfg(feature = "verbose")]
macro_rules! _debug {
	($($args:tt)+) => ({
		use core::fmt::Write;
		if let Err(_) = write!(crate::debug::Console::new(), $($args)+) {
            // we can safely ignore
        }
	});
}

#[cfg(feature = "verbose")]
macro_rules! debug {
	() => ({
        _debug!("\r\n")
    });
	($fmt:expr) => ({
		_debug!(concat!("#ACE: ", $fmt, "\r\n"))
    });
	($fmt:expr, $($args:tt)+) => ({
		_debug!(concat!("#ACE: ", $fmt, "\r\n"), $($args)+)
    });
}

// The below code provides the debug!() macro which will be emmited in the
// output binary only during the build with the verbose flag. For the production
// code the compilar will ignore all debug!() statements
#[macro_export]
#[cfg(not(feature = "verbose"))]
macro_rules! _debug {
    ($( $args:expr ),*) => {};
}

#[macro_export]
#[cfg(not(feature = "verbose"))]
macro_rules! debug {
    ($( $args:expr ),*) => {};
}

pub(crate) use {_debug, debug};

#[cfg(feature = "verbose")]
pub struct Console {}

impl Console {
    pub fn put(c: u8) {
        let ci8: Option<i8> = c.try_into().ok();
        if let Some(v) = ci8 {
            unsafe {
                opensbi_sys::sbi_putc(v);
            }
        }
    }
}

impl Write for Console {
    fn write_str(&mut self, s: &str) -> Result<(), Error> {
        for i in s.bytes() {
            Self::put(i);
        }

        Ok(())
    }
}

impl Console {
    pub fn new() -> Self {
        Console {}
    }
}
