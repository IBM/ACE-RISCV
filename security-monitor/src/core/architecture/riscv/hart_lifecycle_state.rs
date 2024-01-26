// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

/// Hart lifecycle states as documented in the SBI specification of the HSM extension.
#[derive(PartialEq)]
pub enum HartLifecycleState {
    Started,
    Stopped,
    StartPending,
    //
    // StopPending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping pourposes.
    // StopPending,
    Suspended,
    //
    // SuspendPending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping pourposes.
    // SuspendPending,
    //
    // ResumePending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping pourposes.
    // ResumePending,
}
