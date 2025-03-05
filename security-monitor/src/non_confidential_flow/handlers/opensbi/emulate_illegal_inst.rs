// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::specification::CAUSE_ILLEGAL_INSTRUCTION;
use crate::core::architecture::GeneralPurposeRegister;
use crate::core::control_data::HypervisorHart;
use crate::core::timer_controller::TimerController;
use crate::non_confidential_flow::NonConfidentialFlow;

pub struct EmulateIllegalInstruction {
    mstatus: usize,
    mcause: usize,
    mepc: usize,
    mtval: usize,
    vstvec: usize,
    vsstatus: usize,
    htimedelta: usize,
    inst: usize,
    inst_len: usize,
}

impl EmulateIllegalInstruction {
    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        let mstatus = hypervisor_hart.csrs().mstatus.read_from_main_memory();
        let mcause = hypervisor_hart.csrs().mcause.read();
        let mepc = hypervisor_hart.csrs().mepc.read_from_main_memory();
        let mtval = hypervisor_hart.csrs().mtval.read();
        let vstvec = hypervisor_hart.csrs().vstvec.read();
        let vsstatus = hypervisor_hart.csrs().vsstatus.read();
        let mtinst = hypervisor_hart.csrs().mtinst.read();
        let (inst, inst_len) = crate::confidential_flow::handlers::mmio::read_trapped_instruction(mtinst, mepc);
        let htimedelta = hypervisor_hart.csrs().htimedelta;
        Self { mstatus, mcause, mepc, mtval, vstvec, vsstatus, htimedelta, inst, inst_len }
    }

    pub fn handle(self, non_confidential_flow: NonConfidentialFlow) -> NonConfidentialFlow {
        if self.mcause == CAUSE_ILLEGAL_INSTRUCTION.into() {
            return self.emulate_illegal_instruction(non_confidential_flow);
        }
        non_confidential_flow
    }

    pub fn emulate_illegal_instruction(self, mut non_confidential_flow: NonConfidentialFlow) -> NonConfidentialFlow {
        use riscv_decode::Instruction::*;
        let get_rs1_num = |instruction| ((instruction & 0xf8000) >> 15);

        let (csr_value, new_value, do_write, result_gpr_index) = match riscv_decode::decode(self.inst as u32) {
            Ok(Csrrw(t)) => (self.read_csr(t.csr()), t.rs1() as usize, true, t.rd()),
            Ok(Csrrs(t)) => {
                let csr_value = self.read_csr(t.csr());
                (csr_value, csr_value.unwrap_or(0) | (t.rs1() as usize), get_rs1_num(self.inst) != 0, t.rd())
            }
            Ok(Csrrc(t)) => {
                let csr_value = self.read_csr(t.csr());
                (self.read_csr(t.csr()), csr_value.unwrap_or(0) & !(t.rs1() as usize), get_rs1_num(self.inst) != 0, t.rd())
            }
            Ok(Csrrwi(t)) => (self.read_csr(t.csr()), get_rs1_num(self.inst), true, t.rd()),
            Ok(Csrrsi(t)) => {
                let csr_value = self.read_csr(t.csr());
                let rs1_num = get_rs1_num(self.inst);
                (csr_value, csr_value.unwrap_or(0) | rs1_num, rs1_num != 0, t.rd())
            }
            Ok(Csrrci(t)) => {
                let csr_value = self.read_csr(t.csr());
                let rs1_num = get_rs1_num(self.inst);
                (csr_value, csr_value.unwrap_or(0) & !rs1_num, rs1_num != 0, t.rd())
            }
            _ => return non_confidential_flow,
        };

        if do_write {
            non_confidential_flow.hypervisor_hart_mut().csrs_mut().htimedelta = new_value;
            return non_confidential_flow;
        }

        match GeneralPurposeRegister::try_from(result_gpr_index as usize) {
            Ok(v) => match csr_value {
                Some(v2) => non_confidential_flow.hypervisor_hart_mut().gprs_mut().write(v, v2 as usize),
                None => return non_confidential_flow,
            },
            Err(_) => {
                return non_confidential_flow;
            }
        }
        non_confidential_flow.hypervisor_hart_mut().csrs_mut().mepc.add(self.inst_len);
        non_confidential_flow.resume_hypervisor_hart_execution();
    }

    fn read_csr(&self, csr: u32) -> Option<usize> {
        use crate::core::architecture::specification::*;
        use crate::core::architecture::CSR;

        if csr == CSR_TIME.into() {
            return Some(TimerController::read_virt_time(self.htimedelta));
        } else if csr == CSR_CYCLE.into() {
            return Some(CSR.mcycle.read());
        } else if csr == CSR_INSTRET.into() {
            return Some(CSR.minstret.read());
        } else if csr == CSR_HTIMEDELTA.into() {
            return Some(0);
        } else {
            return None;
        }
    }
}
