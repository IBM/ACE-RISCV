// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

//! This module implements a subset of the CoVE's COVH ABI, required to implement the CoVE's deployment model 3.

pub mod destroy_confidential_vm;
pub mod get_info;
pub mod promote_to_confidential_vm;
pub mod run_confidential_hart;
