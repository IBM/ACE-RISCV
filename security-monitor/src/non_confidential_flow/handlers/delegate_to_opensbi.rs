// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{ExposeToHypervisor, OpensbiRequest, OpensbiResult};
use crate::non_confidential_flow::NonConfidentialFlow;
use opensbi_sys::sbi_trap_regs;

extern "C" {
    fn sbi_trap_handler(regs: *mut sbi_trap_regs) -> *mut sbi_trap_regs;
}

/// OpenSBI handler processes regular SBI calls sent by a hypervisor or VMs
pub fn handle(mut non_confidential_flow: NonConfidentialFlow) -> ! {
    let mut request = OpensbiRequest::from_hardware_hart(non_confidential_flow.hardware_hart());
    // We must ensure that the swap is called twice, before and after executing the OpenSBI handler. Otherwise, we end
    // up having incorrect address in mscratch and the context switches to/from the security monitor will not work
    // anymore.
    non_confidential_flow.swap_mscratch();
    unsafe { sbi_trap_handler(request.regs() as *mut _) };
    non_confidential_flow.swap_mscratch();

    let transformation = ExposeToHypervisor::OpensbiResult(OpensbiResult::from_opensbi_handler(request.into_regs()));
    non_confidential_flow.exit_to_hypervisor(transformation)
}
