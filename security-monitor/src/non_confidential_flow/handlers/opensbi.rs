// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToHypervisor, OpensbiRequest, SbiResult};
use crate::error::Error;
use crate::non_confidential_flow::NonConfidentialFlow;
use opensbi_sys::sbi_trap_regs;

extern "C" {
    fn sbi_trap_handler(regs: *mut sbi_trap_regs) -> *mut sbi_trap_regs;
}

/// OpenSBI handler processes regular SBI calls sent by a hypervisor or VMs
pub fn handle(
    mut opensbi_request: OpensbiRequest,
    mut non_confidential_flow: NonConfidentialFlow,
) -> ! {
    let previous_mepc = opensbi_request.regs.mepc.try_into().unwrap_or(0);

    // We must ensure that the swap is called twice, before and after executing the OpenSBI handler. Otherwise, we end
    // up having incorrect address in mscratch and the context switches to/from the security monitor will not work
    // anymore.
    non_confidential_flow.swap_mscratch();
    unsafe { sbi_trap_handler(&mut opensbi_request.regs as *mut _) };
    non_confidential_flow.swap_mscratch();

    let transformation = create_transformation(&opensbi_request.regs, previous_mepc)
        .unwrap_or_else(|e| e.into_non_confidential_transformation());
    non_confidential_flow.exit_to_hypervisor(transformation)
}

fn create_transformation(
    regs: &opensbi_sys::sbi_trap_regs,
    previous_mepc: usize,
) -> Result<ExposeToHypervisor, Error> {
    let a0 = regs.a0.try_into().map_err(|e| Error::SbiArgument(e))?;
    let a1 = regs.a1.try_into().map_err(|e| Error::SbiArgument(e))?;
    let pc_offset = regs.mepc as usize - previous_mepc;
    Ok(ExposeToHypervisor::SbiResult(SbiResult::with_mstatus(
        a0, a1, pc_offset,
    )))
}
