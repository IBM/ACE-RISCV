// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

//! This module implements a subset of the CoVE's COVH ABI required to implement the CoVE's deployment model 3.

pub use destroy_confidential_vm::DestroyConfidentialVm;
pub use get_security_monitor_info::GetSecurityMonitorInfo;
pub use promote_to_confidential_vm::PromoteToConfidentialVm;
pub use run_confidential_hart::RunConfidentialHart;

mod destroy_confidential_vm;
mod get_security_monitor_info;
mod promote_to_confidential_vm;
mod run_confidential_hart;
