// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::error::Error;

pub struct DelegateToConfidentialVm {
    mstatus: usize,
    mcause: usize,
    mepc: usize,
    mtval: usize,
    vstvec: usize,
    vsstatus: usize,
    mtinst: usize,
}

impl DelegateToConfidentialVm {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let mstatus = confidential_hart.csrs().mstatus.read_from_main_memory();
        let mcause = confidential_hart.csrs().mcause.read();
        let mepc = confidential_hart.csrs().mepc.read_from_main_memory();
        let mtval = confidential_hart.csrs().mtval.read();
        let vstvec = confidential_hart.csrs().vstvec.read();
        let vsstatus = confidential_hart.csrs().vsstatus.read();
        let mtinst = confidential_hart.csrs().mtinst.read();

        Self { mstatus, mcause, mepc, mtval, vstvec, vsstatus, mtinst }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        debug!(
            "Delegating mcause={} mepc={:x} mtinst={:x} mstatus={:x} vstvec={:x} vsstatus={:x} to conf vm",
            self.mcause, self.mepc, self.mtinst, self.mstatus, self.vstvec, self.vsstatus
        );
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::DelegateToConfidentialVm(self))
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        let SR_SPP_MASK = 0x00000100;
        let SR_SIE = 0x00000002;
        let SR_SPIE = 0x00000020;

        let mut new_vsstatus = self.vsstatus;
        new_vsstatus &= !SR_SPP_MASK;
        if self.mstatus & SR_SPP_MASK > 0 {
            new_vsstatus |= SR_SPP_MASK;
        }

        /* Change Guest SSTATUS.SPIE bit */
        new_vsstatus &= !SR_SPIE;
        if self.vsstatus & SR_SIE > 0 {
            new_vsstatus |= SR_SPIE;
        }

        /* Clear Guest SSTATUS.SIE bit */
        new_vsstatus &= !SR_SIE;

        /* Update Guest SSTATUS */
        confidential_hart.csrs_mut().vsstatus.write(new_vsstatus);
        /* Update Guest SCAUSE, STVAL, and SEPC */
        confidential_hart.csrs_mut().vscause.write(self.mcause);
        confidential_hart.csrs_mut().vstval.write(self.mtval);
        confidential_hart.csrs_mut().vsepc.write(self.mepc);
        /* Set Guest privilege mode to supervisor */
        confidential_hart.csrs_mut().mstatus.enable_bits_on_saved_value(SR_SPP_MASK);

        confidential_hart.csrs_mut().mepc.save_value_in_main_memory(self.vstvec);
    }
}
