// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::control_status_registers::ReadWriteRiscvCsr;
use crate::core::architecture::specification::{CSR_STIMECMP, CSR_VSTIMECMP};

#[repr(C)]
pub struct SupervisorTimerExtension {
    pub stimecmp: ReadWriteRiscvCsr<CSR_STIMECMP>,
    pub vstimecmp: ReadWriteRiscvCsr<CSR_VSTIMECMP>,
}

impl SupervisorTimerExtension {
    // A constant defined by Sstc extension that defines infinity, i.e., the timer will never interrupt.
    pub const TIMER_INFINITY: usize = usize::MAX - 1;

    pub fn empty() -> Self {
        Self {
            stimecmp: ReadWriteRiscvCsr::new_with_value(Self::TIMER_INFINITY),
            vstimecmp: ReadWriteRiscvCsr::new_with_value(Self::TIMER_INFINITY),
        }
    }

    /// Saves in main memory the sstc state.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the sstc exists
    pub unsafe fn save_in_main_memory(&mut self) {
        self.stimecmp.save_in_main_memory();
        self.vstimecmp.save_in_main_memory();
    }

    /// Restores from main memory the sstc state.
    ///
    /// # Safety
    ///
    /// Caller must ensure that the sstc exists.
    pub unsafe fn restore_from_main_memory(&self) {
        self.stimecmp.restore_from_main_memory();
        self.vstimecmp.restore_from_main_memory();
    }
}
