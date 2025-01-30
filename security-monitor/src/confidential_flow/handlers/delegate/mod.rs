// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::specification::CAUSE_ILLEGAL_INSTRUCTION;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::ConfidentialHart;
use crate::error::Error;

pub use time::TimeRequest;

mod time;

pub struct DelegateToConfidentialVm {
    mstatus: usize,
    mcause: usize,
    mepc: usize,
    mtval: usize,
    vstvec: usize,
    vsstatus: usize,
    inst: usize,
    inst_len: usize,
}

impl DelegateToConfidentialVm {
    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        let mstatus = confidential_hart.csrs().mstatus.read_from_main_memory();
        let mcause = confidential_hart.csrs().mcause.read();
        let mepc = confidential_hart.csrs().mepc.read_from_main_memory();
        let mtval = confidential_hart.csrs().mtval.read();
        let vstvec = confidential_hart.csrs().vstvec.read();
        let vsstatus = confidential_hart.csrs().vsstatus.read();
        let (inst, inst_len) = crate::confidential_flow::handlers::mmio::read_trapped_instruction(confidential_hart);
        Self { mstatus, mcause, mepc, mtval, vstvec, vsstatus, inst, inst_len }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        if self.mcause == CAUSE_ILLEGAL_INSTRUCTION.into() {
            self.emulate_illegal_instruction(confidential_flow)
        } else {
            debug!(
                "Delegating mcause={} mepc={:x} mtinst={:x} mstatus={:x} vstvec={:x} vsstatus={:x} to conf vm",
                self.mcause, self.mepc, self.inst, self.mstatus, self.vstvec, self.vsstatus
            );
            confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::DelegateToConfidentialVm(self))
        }
    }

    pub fn emulate_illegal_instruction(self, mut confidential_flow: ConfidentialFlow) -> ! {
        use riscv_decode::Instruction::*;
        let get_rs1_num = |instruction| ((instruction & 0xf8000) >> 15);

        let (csr_value, _new_value, do_write, result_gpr_index) = match riscv_decode::decode(self.inst as u32) {
            Ok(Csrrw(t)) => (self.read_csr(t.csr()), t.rs1() as usize, true, t.rd()),
            Ok(Csrrs(t)) => {
                let csr_value = self.read_csr(t.csr());
                (csr_value, csr_value | (t.rs1() as usize), get_rs1_num(self.inst) != 0, t.rd())
            }
            Ok(Csrrc(t)) => {
                let csr_value = self.read_csr(t.csr());
                (self.read_csr(t.csr()), csr_value & !(t.rs1() as usize), get_rs1_num(self.inst) != 0, t.rd())
            }
            Ok(Csrrwi(t)) => (self.read_csr(t.csr()), get_rs1_num(self.inst), true, t.rd()),
            Ok(Csrrsi(t)) => {
                let csr_value = self.read_csr(t.csr());
                let rs1_num = get_rs1_num(self.inst);
                (csr_value, csr_value | rs1_num, rs1_num != 0, t.rd())
            }
            Ok(Csrrci(t)) => {
                let csr_value = self.read_csr(t.csr());
                let rs1_num = get_rs1_num(self.inst);
                (csr_value, csr_value & !rs1_num, rs1_num != 0, t.rd())
            }
            _ => confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::DelegateToConfidentialVm(self)),
        };

        if do_write {
            debug!("Emulate illegal instruction: Not supporting CSR write");
        }

        match GeneralPurposeRegister::try_from(result_gpr_index as usize) {
            Ok(v) => {
                confidential_flow.confidential_hart_mut().gprs_mut().write(v, csr_value as usize);
            }
            Err(_) => {
                debug!("Emulate illegal instruction: Invalid GPR {}", result_gpr_index);
            }
        }
        confidential_flow.confidential_hart_mut().csrs_mut().mepc.add(self.inst_len);
        confidential_flow.resume_confidential_hart_execution();
    }

    fn read_csr(&self, csr: u32) -> usize {
        use crate::core::architecture::specification::*;
        use crate::core::architecture::CSR;

        if csr == CSR_TIME.into() {
            return (unsafe { (0x200BFF8 as *const u64).read_volatile() }) as usize;
        } else if csr == CSR_CYCLE.into() {
            return CSR.mcycle.read();
        } else if csr == CSR_INSTRET.into() {
            return CSR.minstret.read();
        } else {
            debug!("Emulate illegal instruction: Unsupported CSR: {:x}", csr);
            return 0;
        }
    }

    pub fn apply_to_confidential_hart(&self, confidential_hart: &mut ConfidentialHart) {
        use crate::core::architecture::specification::CSR_MSTATUS_MPP;
        let SR_SPP_MASK = 0x00000100;
        let SR_SIE = 0x00000002;
        let SR_SPIE = 0x00000020;

        let mut new_vsstatus = self.vsstatus;
        new_vsstatus &= !SR_SPP_MASK;
        if self.mstatus & (0b11 << CSR_MSTATUS_MPP) == (1 << CSR_MSTATUS_MPP) {
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
        confidential_hart.csrs_mut().mstatus.enable_bits_on_saved_value((1 << CSR_MSTATUS_MPP));

        confidential_hart.csrs_mut().mepc.save_value_in_main_memory(self.vstvec);
    }
}
