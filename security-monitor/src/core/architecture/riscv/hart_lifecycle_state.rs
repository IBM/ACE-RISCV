// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

/// Hart lifecycle states are partially based on the SBI specification of the HSM extension. We do not support all of
/// the SBI's HSM states because there is no need for that, i.e., the security monitor can directly stop or suspend a
/// confidential hart without the need to go through the StopPending or SuspendPending states. We introduced one
/// additional lifecycle state `Shutdown` that represents a final state of the confidential hart that has been shutdown
/// as part of the `VM shutdown` procedure.
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
    //
    // Shutdown state does not exist in the SBI's HSM extension. We use it to represent a confidential hart that has
    // been shutdown and cannot be used anymore. When all confidential harts are shutdown the confidential VM can be
    // removed from the control data.
    Shutdown,
}
