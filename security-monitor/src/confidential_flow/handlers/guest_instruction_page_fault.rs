// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::architecture::{GpRegister, HartArchitecturalState};
use crate::core::transformations::{ExposeToConfidentialVm, SbiResult};
use crate::error::Error;

/// Handles the situation in which a confidential hart trapped into the security monitor but the security monitor does
/// not support such exception. For example, a confidential hart could trap after making a not supported SBI call.
pub fn handle(confidential_hart_state: HartArchitecturalState, confidential_flow: ConfidentialFlow) -> ! {
    let a0 = confidential_hart_state.gpr(GpRegister::a0);
    let a1 = confidential_hart_state.gpr(GpRegister::a1);
    let a2 = confidential_hart_state.gpr(GpRegister::a2);
    let a3 = confidential_hart_state.gpr(GpRegister::a3);

    let mtval = confidential_hart_state.mtval;
    let mtval2 = confidential_hart_state.mtval2;
    let fault_addr = (mtval2 << 2) | (mtval & 0x3);

    let htinst = read_htinst();
    let mtinst = read_mtinst();

    debug!(
        "CVM debug: GuestInstructionPageFault htinst={:x} mtinst={:x} fault_addr={:x} [mepc={:x}]",
        htinst, mtinst, confidential_hart_state.mepc, fault_addr
    );
    let transformation = ExposeToConfidentialVm::SbiResult(SbiResult::success(0));
    confidential_flow.exit_to_confidential_hart(transformation)
}

fn read_htinst() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x64a, x0"), out(reg) r);
    }
    r
}

fn read_mtinst() -> usize {
    let r: usize;
    unsafe {
        core::arch::asm!(concat!("csrrs {0}, 0x34a, x0"), out(reg) r);
    }
    r
}
