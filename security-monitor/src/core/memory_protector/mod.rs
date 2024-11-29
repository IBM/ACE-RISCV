// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use confidential_vm_memory_protector::ConfidentialVmMemoryProtector;
pub use hypervisor_memory_protector::HypervisorMemoryProtector;

mod confidential_vm_memory_protector;
mod hypervisor_memory_protector;
