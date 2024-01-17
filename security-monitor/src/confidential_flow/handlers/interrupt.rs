// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::transformations::{ExposeToHypervisor, InterruptRequest};
use crate::error::Error;

// machine-level software interrupt
const MSIP: usize = 3;
const MSIP_MASK: usize = 1 << MSIP;
// machine timer interrupt pending
const MTIP: usize = 7;
const MTIP_MASK: usize = 1 << MTIP;
// machine external interrupt pending
const MEIP: usize = 11;
const MEIP_MASK: usize = 1 << MEIP;
// supervisor-level software interrupt
const SSIP: usize = 1;
const SSIP_MASK: usize = 1 << SSIP;
// supervisor-level timer interrupt pending
const STIP: usize = 5;
const STIP_MASK: usize = 1 << STIP;
// supervisor-level external interrupt pending
const SEIP: usize = 9;
const SEIP_MASK: usize = 1 << SEIP;

/// Interrupts are reflected to the hypervisor because it has to decide what to
/// do with them.
pub fn handle(mut confidential_flow: ConfidentialFlow) -> ! {
    // TODO: handle interrupts targeted for confidential VM by reflecting them
    // directly to the confidential VM
    let mip = riscv::register::mip::read().bits();
    let interrupt_code = if mip & MEIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(MEIP - 2)
    } else if mip & MSIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(MSIP - 2)
    } else if mip & MTIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(MTIP - 2)
    } else if mip & SEIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(SEIP)
    } else if mip & SSIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(SSIP)
    } else if mip & STIP_MASK > 0 {
        // TODO: clear the bit in mip
        Ok(STIP)
    } else {
        Err(Error::NotSupportedInterrupt())
    };

    // One of the reasons why the confidential hart was interrupted with SSIP is that it got InterHartRequest from
    // another confidential hart. If this is the case, we must process all queued requests before resuming confidential
    // hart's execution.
    if interrupt_code.as_ref().is_ok_and(|v| v == &SSIP) {
        confidential_flow.process_inter_hart_requests();
    }

    let transformation = match interrupt_code {
        Ok(v) => ExposeToHypervisor::InterruptRequest(InterruptRequest::new(v)),
        Err(error) => error.into_non_confidential_transformation(),
    };

    confidential_flow.into_non_confidential_flow().exit_to_hypervisor(transformation)
}
