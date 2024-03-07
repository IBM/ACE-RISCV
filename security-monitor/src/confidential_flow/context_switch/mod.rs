// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::ConfidentialFlow;
use crate::core::control_data::HardwareHart;

/// Creates the mutable reference to HardwareHart by casting a raw pointer obtained from the context switch (assembly)
/// and then jumps to the `router`.
///
/// This is a private function, not accessible to safe Rust but accessible to the assembly code performing the context
/// switch.
#[no_mangle]
extern "C" fn enter_from_confidential_hart(hart_ptr: *mut HardwareHart) -> ! {
    let hart = unsafe { hart_ptr.as_mut().expect(crate::error::CTX_SWITCH_ERROR_MSG) };
    ConfidentialFlow::create(hart).route();
}

core::arch::global_asm!(
    include_str!("enter_from_confidential_hart.S"),
    include_str!("exit_to_confidential_hart.S"),

    HART_RA_OFFSET = const crate::core::control_data::HART_RA_OFFSET,
    HART_SP_OFFSET = const crate::core::control_data::HART_SP_OFFSET,
    HART_GP_OFFSET = const crate::core::control_data::HART_GP_OFFSET,
    HART_TP_OFFSET = const crate::core::control_data::HART_TP_OFFSET,
    HART_T0_OFFSET = const crate::core::control_data::HART_T0_OFFSET,
    HART_T1_OFFSET = const crate::core::control_data::HART_T1_OFFSET,
    HART_T2_OFFSET = const crate::core::control_data::HART_T2_OFFSET,
    HART_S0_OFFSET = const crate::core::control_data::HART_S0_OFFSET,
    HART_S1_OFFSET = const crate::core::control_data::HART_S1_OFFSET,
    HART_A0_OFFSET = const crate::core::control_data::HART_A0_OFFSET,
    HART_A1_OFFSET = const crate::core::control_data::HART_A1_OFFSET,
    HART_A2_OFFSET = const crate::core::control_data::HART_A2_OFFSET,
    HART_A3_OFFSET = const crate::core::control_data::HART_A3_OFFSET,
    HART_A4_OFFSET = const crate::core::control_data::HART_A4_OFFSET,
    HART_A5_OFFSET = const crate::core::control_data::HART_A5_OFFSET,
    HART_A6_OFFSET = const crate::core::control_data::HART_A6_OFFSET,
    HART_A7_OFFSET = const crate::core::control_data::HART_A7_OFFSET,
    HART_S2_OFFSET = const crate::core::control_data::HART_S2_OFFSET,
    HART_S3_OFFSET = const crate::core::control_data::HART_S3_OFFSET,
    HART_S4_OFFSET = const crate::core::control_data::HART_S4_OFFSET,
    HART_S5_OFFSET = const crate::core::control_data::HART_S5_OFFSET,
    HART_S6_OFFSET = const crate::core::control_data::HART_S6_OFFSET,
    HART_S7_OFFSET = const crate::core::control_data::HART_S7_OFFSET,
    HART_S8_OFFSET = const crate::core::control_data::HART_S8_OFFSET,
    HART_S9_OFFSET = const crate::core::control_data::HART_S9_OFFSET,
    HART_S10_OFFSET = const crate::core::control_data::HART_S10_OFFSET,
    HART_S11_OFFSET = const crate::core::control_data::HART_S11_OFFSET,
    HART_T3_OFFSET = const crate::core::control_data::HART_T3_OFFSET,
    HART_T4_OFFSET = const crate::core::control_data::HART_T4_OFFSET,
    HART_T5_OFFSET = const crate::core::control_data::HART_T5_OFFSET,
    HART_T6_OFFSET = const crate::core::control_data::HART_T6_OFFSET,

    HART_MEPC_OFFSET = const crate::core::control_data::HART_MEPC_OFFSET,
    HART_MSTATUS_OFFSET = const crate::core::control_data::HART_MSTATUS_OFFSET,

    HART_STACK_ADDRESS_OFFSET = const crate::core::control_data::HART_STACK_ADDRESS_OFFSET,
);
