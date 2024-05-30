// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![allow(unused)]

/// State of the security monitor communicated to the hypervisor. This structure is defined in CoVE specification.
#[repr(u32)]
pub enum SecurityMonitorState {
    NotLoaded = 0,
    Loaded = 1,
    Ready = 2,
}

/// Information written by the security monitor to the hypervisor memory, representing the state of the security monitor. This structure is
/// defined in CoVE specification.
#[repr(C)]
pub struct SecurityMonitorInfo {
    pub security_monitor_state: SecurityMonitorState,
    pub security_monitor_version: u32,
    pub state_pages: u64,
    pub max_vcpus: u64,
    pub vcpu_state_pages: u64,
}
