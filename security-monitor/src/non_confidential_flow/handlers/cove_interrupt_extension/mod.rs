// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

//! This module implements a subset of the CoVE's COVI ABI required to implement the CoVE's deployment model 3.

pub use inject_external_interrupt::InjectExternalInterrupt;

mod inject_external_interrupt;
