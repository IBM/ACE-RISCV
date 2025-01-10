// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]
use crate::core::architecture::{GeneralPurposeRegister, HartArchitecturalState, CSR};
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
pub fn __printout_metadata(svm_id: usize) {}

#[cfg(feature = "verbose")]
pub fn __print_pmp_configuration() {
    use crate::core::architecture::specification::PMP_ADDRESS_SHIFT;
    let pmpcfg0 = CSR.pmpcfg0.read();

    // debug!("mseccfg: {:b}", CSR.mseccfg.read());
    debug!("PMP0: {:x} ({:b})", CSR.pmpaddr0.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF);
    debug!("PMP1: {:x} ({:b})", CSR.pmpaddr1.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF00);
    debug!("PMP2: {:x} ({:b})", CSR.pmpaddr2.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF0000);
    debug!("PMP3: {:x} ({:b})", CSR.pmpaddr3.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF000000);
    debug!("PMP4: {:x} ({:b})", CSR.pmpaddr4.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF00000000);
    debug!("PMP5: {:x} ({:b})", CSR.pmpaddr5.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF0000000000);
    debug!("PMP6: {:x} ({:b})", CSR.pmpaddr6.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF000000000000);
    debug!("PMP7: {:x} ({:b})", CSR.pmpaddr7.read() << PMP_ADDRESS_SHIFT, pmpcfg0 & 0xFF00000000000000);
}

#[macro_export]
#[cfg(not(feature = "verbose"))]
pub fn __print_pmp_configuration() {}

#[cfg(feature = "verbose")]
pub fn __print_hart_state(state: &HartArchitecturalState) {
    debug!("Hart state:");
    // for i in 0..8 {
    //     let gpr_id = i * 4;
    //     let v0 = state.gprs().read(GeneralPurposeRegister::try_from(gpr_id).unwrap());
    //     let v1 = state.gprs().read(GeneralPurposeRegister::try_from(gpr_id + 1).unwrap());
    //     let v2 = state.gprs().read(GeneralPurposeRegister::try_from(gpr_id + 2).unwrap());
    //     let v3 = state.gprs().read(GeneralPurposeRegister::try_from(gpr_id + 3).unwrap());
    //     debug!("x{}: {:16x}\tx{}: {:16x}\tx{}: {:16x}\tx{}: {:16x}", gpr_id, v0, gpr_id + 1, v1, gpr_id + 2, v2, gpr_id + 3, v3);
    // }

    debug!("mepc (from main memory) = {:x}", state.csrs().mepc.read_from_main_memory());
    debug!("mepc = {:16x}", state.csrs().mepc.read());
    debug!("mcause = {:16x}", state.csrs().mcause.read());
    debug!("medeleg = {:16x}", state.csrs().medeleg.read());
    debug!("mideleg = {:16x}", state.csrs().mideleg.read());
    debug!("mie = {:16x}", state.csrs().mie.read());
    debug!("mip = {:16x}", state.csrs().mip.read());
    debug!("mstatus = {:16x}", state.csrs().mstatus.read());
    debug!("mtinst = {:16x}", state.csrs().mtinst.read());
    debug!("mtval = {:16x}", state.csrs().mtval.read());
    debug!("mtval2 = {:16x}", state.csrs().mtval2.read());
    // debug!("mtvec = {:16x}", state.csrs().mtvec.read());
    // debug!("mscratch = {:16x}", state.csrs().mscratch.read());
    // debug!("sstatus = {:16x}", state.csrs().sstatus.read());
    // debug!("sie = {:16x}", state.csrs().sie.read());
    // debug!("stvec = {:16x}", state.csrs().stvec.read());
    // debug!("scounteren = {:16x}", state.csrs().scounteren.read());
    // debug!("senvcfg = {:16x}", state.csrs().senvcfg.read());
    // debug!("sscratch = {:16x}", state.csrs().sscratch.read());
    // debug!("sepc = {:16x}", state.csrs().sepc.read());
    // debug!("scause = {:16x}", state.csrs().scause.read());
    // debug!("stval = {:16x}", state.csrs().stval.read());
    // debug!("sip = {:16x}", state.csrs().sip.read());
    // debug!("satp = {:16x}", state.csrs().satp.read());
    // debug!("scontext = {:16x}", state.csrs().scontext.read());
    // debug!("hstatus = {:16x}", state.csrs().hstatus.read());
    debug!("hedeleg = {:16x}", state.csrs().hedeleg.read());
    // debug!("hideleg = {:16x}", state.csrs().hideleg.read());
    // debug!("hie = {:16x}", state.csrs().hie.read());
    // debug!("hcounteren = {:16x}", state.csrs().hcounteren.read());
    // debug!("hgeie = {:16x}", state.csrs().hgeie.read());
    // debug!("htval = {:16x}", state.csrs().htval.read());
    // debug!("hip = {:16x}", state.csrs().hip.read());
    // debug!("hvip = {:16x}", state.csrs().hvip.read());
    debug!("htinst = {:16x}", state.csrs().htinst.read());
    // debug!("hgeip = {:16x}", state.csrs().hgeip.read());
    // debug!("hgatp = {:16x}", state.csrs().hgatp.read());
    // debug!("hcontext = {:16x}", state.csrs().hcontext.read());
    // debug!("htimedelta = {:16x}", state.csrs().htimedelta.read());
    // debug!("vsstatus = {:16x}", state.csrs().vsstatus.read());
    // debug!("vsie = {:16x}", state.csrs().vsie.read());
    // debug!("vsip = {:16x}", state.csrs().vsip.read());
    // debug!("vstvec = {:16x}", state.csrs().vstvec.read());
    // debug!("vsscratch = {:16x}", state.csrs().vsscratch.read());
    // debug!("vsepc = {:16x}", state.csrs().vsepc.read());
    // debug!("vscause = {:16x}", state.csrs().vscause.read());
    // debug!("vstval = {:16x}", state.csrs().vstval.read());
    // debug!("vsatp = {:16x}", state.csrs().vsatp.read());
}

#[macro_export]
#[cfg(not(feature = "verbose"))]
pub fn __print_hart_state(state: &HartArchitecturalState) {}

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
