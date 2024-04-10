// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]

/// Hart lifecycle states are partially based on the SBI specification of the HSM extension. We do not support all of
/// the SBI's HSM states because there is no need for that, i.e., the security monitor can directly stop or suspend a
/// confidential hart without the need to go through the StopPending or SuspendPending states. We introduced one
/// additional lifecycle state `Shutdown` that represents a final state of the confidential hart that has been shutdown
/// as part of the `VM shutdown` procedure.
#[derive(PartialEq, Clone)]
pub enum HartLifecycleState {
    Started,
    Stopped,
    // StartPending is never used because the security monitor starts the hart directly and only informs a hypervisor
    // about it for the bookkeeping purposes.
    // StartPending,
    //
    // StopPending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping purposes.
    // StopPending,
    Suspended,
    //
    // SuspendPending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping purposes.
    // SuspendPending,
    //
    // ResumePending is never used because the security monitor stops the hart directly and only informs a hypervisor
    // about it for the bookkeeping purposes.
    // ResumePending,
    //
    // Shutdown state does not exist in the SBI's HSM extension. We use it to represent a confidential hart that has
    // been shutdown and cannot be used anymore. When all confidential harts are shutdown the confidential VM can be
    // removed from the control data.
    Shutdown,
}

impl HartLifecycleState {
    /// Returns the HSM state id, which is a number assigned to a specific state defined by the SBI HSM extension specification.
    pub fn sbi_code(&self) -> usize {
        match self {
            Self::Started => 0,
            Self::Stopped => 1,
            Self::Suspended => 4,
            // Shutdown state is not part of the SBI spec, we represent it as the `Stopped` state.
            Self::Shutdown => 1,
        }
    }
}
