// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::transformations::{SbiHsmHartStart, SbiHsmHartSuspend};

pub enum HartLifecycleStateTransition {
    StoppedToStartPending(SbiHsmHartStart),
    StartedToSuspended(SbiHsmHartSuspend),
    SuspendedToStarted(),
    StartedToStopped(),
}
