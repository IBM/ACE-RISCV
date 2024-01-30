// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{SbiHsmHartStart, SbiHsmHartSuspend};

/// Represents possible state transisitons in the lifecycle finite state machine (FSM) of a confidential hart.
pub enum HartLifecycleStateTransition {
    StoppedToStartPending(SbiHsmHartStart),
    StartedToSuspended(SbiHsmHartSuspend),
    SuspendedToStarted(),
    StartedToStopped(),
    ToShutdown(),
}
