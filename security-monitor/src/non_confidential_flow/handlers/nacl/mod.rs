// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

//! This module implements a subset of the NACL ABI required to implement the CoVE's deployment model 3.

pub use nacl_probe_feature::NaclProbeFeature;
pub use nacl_setup_shared_memory::NaclSetupSharedMemory;

mod nacl_probe_feature;
mod nacl_setup_shared_memory;
