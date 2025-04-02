// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
use core::convert::TryInto;
use core::fmt::{Error, Write};

#[macro_export]
macro_rules! ensure {
    ($cond:expr, $error:expr) => {
        if !$cond {
            Err($error)
        } else {
            Ok(())
        }
    };
}

#[macro_export]
macro_rules! ensure_not {
    ($cond:expr, $error:expr) => {
        if $cond {
            Err($error)
        } else {
            Ok(())
        }
    };
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
    () => {{}};
    ($fmt:expr) => {{}};
    ($fmt:expr, $($args:tt)+) => {{}};
}

pub(crate) use {_debug, debug};

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
