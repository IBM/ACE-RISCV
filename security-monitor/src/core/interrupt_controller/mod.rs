// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::Error;
use spin::{Once, RwLock, RwLockReadGuard};

const NOT_INITIALIZED_INTERRUPT_CONTROLLER: &str =
    "Bug. Could not access interrupt controller because it is not initialized";

/// A static global structure for the interrupt controller that abstract the functionality needed by the security
/// monitor to interrupt harts. Once<> guarantees that it the interrupt controller can only be initialized once.
static INTERRUPT_CONTROLLER: Once<RwLock<InterruptController>> = Once::new();

extern "C" {
    fn sbi_ipi_send_smode(hmask: usize, hbase: usize) -> usize;
}

pub struct InterruptController {}

impl<'a> InterruptController {
    pub unsafe fn initialize() -> Result<(), Error> {
        let interrupt_controller = unsafe { Self::new() }?;
        assure_not!(INTERRUPT_CONTROLLER.is_completed(), Error::Reinitialization())?;
        INTERRUPT_CONTROLLER.call_once(|| RwLock::new(interrupt_controller));
        Ok(())
    }

    unsafe fn new() -> Result<Self, Error> {
        Ok(Self {})
    }

    pub fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, InterruptController>) -> Result<F, Error> {
        op(&INTERRUPT_CONTROLLER.get().expect(NOT_INITIALIZED_INTERRUPT_CONTROLLER).read())
    }

    pub fn send_ipi(&self, hart_id: usize) -> Result<(), Error> {
        debug!("Sending an IPI to physical hart: {}", hart_id);

        let hart_mask = 1;
        let hart_mask_base = hart_id;
        // for now we rely on the underlying OpenSBI to send IPIs to hardware harts
        match unsafe { sbi_ipi_send_smode(hart_mask, hart_mask_base) } {
            0 => Ok(()),
            _ => Err(Error::InterruptSendingError()),
        }
    }
}
