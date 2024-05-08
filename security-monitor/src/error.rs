// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use core::num::TryFromIntError;
use pointers_utility::PointerError;
use thiserror_no_std::Error;

pub const NOT_INITIALIZED_HART: &str = "Physical hart does not have a state allocated in the confidential memory. There is an error in the security monitor initialization vector";

pub const NOT_INITIALIZED_HARTS: &str = "Bug. Could not set mscratch before initializing memory region for HARTs states";

pub const NOT_INITIALIZED_CONTROL_DATA: &str = "Bug. Could not access the control data static variable because it is not initialized";

#[derive(Error, Debug)]
pub enum Error {
    #[error("security monitor initialization error")]
    Init(InitType),
    #[error("Cannot initialize memory as it has already been initialized")]
    Reinitialization(),
    #[error("Not supported hardware")]
    NotSupportedHardware(HardwareFeatures),
    #[error("Error while searching FDT for a property")]
    FdtParsing(),
    #[error("Could not convert SBI argument to usize: {0}")]
    SbiArgument(#[from] TryFromIntError),
    #[error("Not enough memory to allocate on heap")]
    OutOfMemory(),
    #[error("Not enough memory to allocate a page")]
    OutOfPages(),
    #[error("Unsupported amount of memory")]
    UnsupportedMemorySize(),
    #[error("Page table error")]
    PageTableConfiguration(),
    #[error("Address translation failed")]
    AddressTranslationFailed(),
    #[error("Page Table is corrupted")]
    PageTableCorrupted(),
    #[error("Invalid argument")]
    InvalidArgument(),
    #[error("Reached a maximum number of confidential VMs")]
    TooManyConfidentialVms(),
    #[error("Unsupported paging mode")]
    UnsupportedPagingMode(),
    #[error("Memory access not authorized")]
    MemoryAccessAuthorization(),
    #[error("There is a pending request")]
    PendingRequest(),
    #[error("Invalid Hart ID")]
    InvalidHartId(),
    #[error("Exceeded the max number of harts per VM")]
    InvalidNumberOfHartsInFdt(),
    #[error("Invalid confidential VM ID")]
    InvalidConfidentialVmId(),
    #[error("vHart is running")]
    HartAlreadyRunning(),
    #[error("Hart is not executable")]
    HartNotExecutable(),
    #[error("Invalid riscv instruction: {0:x}")]
    InvalidRiscvInstruction(usize),
    #[error("Invalid ecall extid: {0} fid: {1}")]
    InvalidCall(usize, usize),
    #[error("Internal error")]
    Pointer(#[from] PointerError),
    #[error("Reached max number of remote hart requests")]
    ReachedMaxNumberOfRemoteHartRequests(),
    #[error("Sending interrupt error")]
    InterruptSendingError(),
    // SBI HSM extension related errors
    #[error("Cannot start a confidential hart because it is not in the Stopped state.")]
    CannotStartNotStoppedHart(),
    #[error("Cannot stop a confidential hart because it is not in the Started state.")]
    CannotStopNotStartedHart(),
    #[error("Cannot suspend a confidential hart because it is not in the Started state.")]
    CannotSuspedNotStartedHart(),
    #[error("Cannot start a confidential hart because it is not in the Suspended state.")]
    CannotStartNotSuspendedHart(),
    #[error("Incorrectly aligned authentication blob")]
    AuthBlobNotAlignedTo64Bits(),
    #[error("Authentication blob size is invalid.")]
    AuthBlobInvalidSize(),
    #[error("Address not properly aligned")]
    AddressNotProperlyAligned(),
    #[error("FDT size is invalid. Expecting at least 40 bytes and maximum 40960 bytes")]
    FdtInvalidSize(),
    #[error("Device Tree Error")]
    DeviceTreeError(#[from] flattened_device_tree::FdtError),
}

impl Error {
    pub fn code(&self) -> usize {
        0x1000
    }
}

#[derive(Error, Debug)]
pub enum InitType {
    #[error("Too little memory")]
    NotEnoughMemory,
    #[error("Invalid memory boundaries")]
    MemoryBoundary,
}

#[derive(Error, Debug)]
pub enum HardwareFeatures {
    #[error("ACE requires 64-bit processor")]
    InvalidCpuArch,
    #[error("CPU does not support the required ISA extension")]
    NoCpuExtension,
    #[error("Not enough PMPs")]
    NotEnoughPmps,
}
