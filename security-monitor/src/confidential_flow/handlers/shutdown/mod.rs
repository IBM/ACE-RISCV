// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use shutdown_confidential_hart::shutdown_confidential_hart;
pub use shutdown_vm::ShutdownRequest;

mod shutdown_confidential_hart;
mod shutdown_vm;
