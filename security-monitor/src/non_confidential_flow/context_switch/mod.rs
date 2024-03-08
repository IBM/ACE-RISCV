// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::control_data::HardwareHart;
use crate::non_confidential_flow::NonConfidentialFlow;

/// This function is private and only the assembly code can call it when making
/// the context switch from the confidential VM to the security monitor.
#[no_mangle]
extern "C" fn enter_from_hypervisor_or_vm(hart_ptr: *mut HardwareHart) -> ! {
    let hardware_hart = unsafe { hart_ptr.as_mut().expect(crate::error::CTX_SWITCH_ERROR_MSG) };
    NonConfidentialFlow::create(hardware_hart).route()
}

core::arch::global_asm!(
    include_str!("enter_from_hypervisor_or_vm.S"),
    include_str!("exit_to_hypervisor.S"),

    HART_RA_OFFSET = const crate::core::architecture::HART_RA_OFFSET,
    HART_SP_OFFSET = const crate::core::architecture::HART_SP_OFFSET,
    HART_GP_OFFSET = const crate::core::architecture::HART_GP_OFFSET,
    HART_TP_OFFSET = const crate::core::architecture::HART_TP_OFFSET,
    HART_T0_OFFSET = const crate::core::architecture::HART_T0_OFFSET,
    HART_T1_OFFSET = const crate::core::architecture::HART_T1_OFFSET,
    HART_T2_OFFSET = const crate::core::architecture::HART_T2_OFFSET,
    HART_S0_OFFSET = const crate::core::architecture::HART_S0_OFFSET,
    HART_S1_OFFSET = const crate::core::architecture::HART_S1_OFFSET,
    HART_A0_OFFSET = const crate::core::architecture::HART_A0_OFFSET,
    HART_A1_OFFSET = const crate::core::architecture::HART_A1_OFFSET,
    HART_A2_OFFSET = const crate::core::architecture::HART_A2_OFFSET,
    HART_A3_OFFSET = const crate::core::architecture::HART_A3_OFFSET,
    HART_A4_OFFSET = const crate::core::architecture::HART_A4_OFFSET,
    HART_A5_OFFSET = const crate::core::architecture::HART_A5_OFFSET,
    HART_A6_OFFSET = const crate::core::architecture::HART_A6_OFFSET,
    HART_A7_OFFSET = const crate::core::architecture::HART_A7_OFFSET,
    HART_S2_OFFSET = const crate::core::architecture::HART_S2_OFFSET,
    HART_S3_OFFSET = const crate::core::architecture::HART_S3_OFFSET,
    HART_S4_OFFSET = const crate::core::architecture::HART_S4_OFFSET,
    HART_S5_OFFSET = const crate::core::architecture::HART_S5_OFFSET,
    HART_S6_OFFSET = const crate::core::architecture::HART_S6_OFFSET,
    HART_S7_OFFSET = const crate::core::architecture::HART_S7_OFFSET,
    HART_S8_OFFSET = const crate::core::architecture::HART_S8_OFFSET,
    HART_S9_OFFSET = const crate::core::architecture::HART_S9_OFFSET,
    HART_S10_OFFSET = const crate::core::architecture::HART_S10_OFFSET,
    HART_S11_OFFSET = const crate::core::architecture::HART_S11_OFFSET,
    HART_T3_OFFSET = const crate::core::architecture::HART_T3_OFFSET,
    HART_T4_OFFSET = const crate::core::architecture::HART_T4_OFFSET,
    HART_T5_OFFSET = const crate::core::architecture::HART_T5_OFFSET,
    HART_T6_OFFSET = const crate::core::architecture::HART_T6_OFFSET,

    HART_MEPC_OFFSET = const crate::core::architecture::HART_MEPC_OFFSET,
    HART_MSTATUS_OFFSET = const crate::core::architecture::HART_MSTATUS_OFFSET,

    HART_STACK_ADDRESS_OFFSET = const crate::core::control_data::HART_STACK_ADDRESS_OFFSET,
);
