// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::*;
use thiserror_no_std::Error;

#[derive(Error, Debug)]
pub enum Error {
    /* Initialization-related errors */
    #[error("Security monitor initialization error: Too little memory")]
    NotEnoughMemory(),
    #[error("Too much memory")]
    TooMuchMemory(),
    #[error("Security monitor initialization error: Invalid memory boundaries")]
    InvalidMemoryBoundary(),
    #[error("BUG: Cannot reinitialize static components")]
    Reinitialization(),
    #[error("Not supported hardware: ACE requires 64-bit processor")]
    InvalidCpuArch(),
    #[error("Not supported hardware: CPU does not support the required ISA extension")]
    MissingCpuExtension(),
    #[error("Not supported hardware: Not enough PMPs")]
    NotEnoughPmps(),
    #[error("Error while searching FDT for a property")]
    FdtParsing(),

    /* Confidential VM creation-related errors */
    #[error("Page table error")]
    PageTableConfiguration(),
    #[error("Invalid address, could not translate it using the given page table configuration")]
    AddressTranslationFailed(),
    #[error("Given page table structure is corrupted")]
    PageTableCorrupted(),
    #[error("Reached a maximum number of confidential VMs")]
    TooManyConfidentialVms(),
    #[error("Unsupported paging mode")]
    UnsupportedPagingMode(),
    #[error("FDT size is invalid. Expecting at least 40 bytes and maximum 40960 bytes")]
    FdtInvalidSize(),
    #[error("Exceeded the max number of harts per VM")]
    InvalidNumberOfHartsInFdt(),
    #[error("Incorrectly aligned authentication blob")]
    AuthBlobNotAlignedTo64Bits(),
    #[error("Authentication blob size is invalid.")]
    AuthBlobInvalidSize(),

    /* SBI invalid address */
    #[error("Address is not aligned")]
    AddressNotAligned(),
    #[error("Address is not in confidential memory")]
    AddressNotInConfidentialMemory(),
    #[error("Address is not in non-confidential memory")]
    AddressNotInNonConfidentialMemory(),
    #[error("Invalid argument")]
    InvalidParameter(),
    #[error("Internal error")]
    Pointer(#[from] pointers_utility::PointerError),

    /* SBI invalid parameters */
    #[error("Invalid confidential VM ID")]
    InvalidConfidentialVmId(),
    #[error("Invalid hart id parameter")]
    InvalidHartId(),
    #[error("Confidential hart is already running")]
    HartAlreadyRunning(),
    #[error("Invalid hart id, the corresponding hart is not executable")]
    HartNotExecutable(),
    #[error("Not supported SBI extension {0} or function {1}")]
    InvalidCall(usize, usize),
    #[error("Device Tree Error")]
    DeviceTreeError(#[from] flattened_device_tree::FdtError),
    #[error("Mmio region overlaps with a region already defined in the past")]
    OverlappingMmioRegion(),

    /* SBI HSM extension-related errors */
    #[error("Cannot start a confidential hart because it is not in the Stopped state.")]
    CannotStartNotStoppedHart(),
    #[error("Cannot stop a confidential hart because it is not in the Started state.")]
    CannotStopNotStartedHart(),
    #[error("Cannot suspend a confidential hart because it is not in the Started state.")]
    CannotSuspedNotStartedHart(),
    #[error("Cannot start a confidential hart because it is not in the Suspended state.")]
    CannotStartNotSuspendedHart(),

    /* MMIO-related errors */
    #[error("Could not decode compressed RISC-V instruction: {0:x}")]
    InvalidCompressedRiscvInstruction(usize),

    /* Internal errors exposed to the outside as a failure */
    #[error("The operation failed for unknown reasons")]
    Failed(),
    #[error("Not enough memory to allocate on heap")]
    OutOfMemory(),
    #[error("Not enough memory to allocate a page")]
    OutOfPages(),
    #[error("There is a pending request")]
    PendingRequest(),
    #[error("Reached max number of remote hart requests")]
    ReachedMaxNumberOfRemoteHartRequests(),
    #[error("Reached max number of registered MMIO regions")]
    ReachedMaxNumberOfMmioRegions(),
    #[error("Could not send an IPI, error code: {0}")]
    InterruptSendingError(usize),
}

impl Error {
    pub fn sbi_error_code(&self) -> usize {
        match &self {
            Self::AddressNotAligned() => SBI_ERR_INVALID_ADDRESS as usize,
            Self::AddressNotInConfidentialMemory() => SBI_ERR_INVALID_ADDRESS as usize,
            Self::AddressNotInNonConfidentialMemory() => SBI_ERR_INVALID_ADDRESS as usize,
            Self::AddressTranslationFailed() => SBI_ERR_INVALID_ADDRESS as usize,
            Self::Pointer(_) => SBI_ERR_INVALID_ADDRESS as usize,

            Self::InvalidParameter() => SBI_ERR_INVALID_PARAM as usize,
            Self::InvalidConfidentialVmId() => SBI_ERR_INVALID_PARAM as usize,
            Self::InvalidHartId() => SBI_ERR_INVALID_PARAM as usize,
            Self::HartAlreadyRunning() => SBI_ERR_INVALID_PARAM as usize,
            Self::HartNotExecutable() => SBI_ERR_INVALID_PARAM as usize,
            Self::InvalidCall(_, _) => SBI_ERR_INVALID_PARAM as usize,
            Self::PageTableCorrupted() => SBI_ERR_INVALID_PARAM as usize,
            Self::UnsupportedPagingMode() => SBI_ERR_INVALID_PARAM as usize,
            Self::FdtInvalidSize() => SBI_ERR_INVALID_PARAM as usize,
            Self::InvalidNumberOfHartsInFdt() => SBI_ERR_INVALID_PARAM as usize,
            Self::AuthBlobNotAlignedTo64Bits() => SBI_ERR_INVALID_PARAM as usize,
            Self::AuthBlobInvalidSize() => SBI_ERR_INVALID_PARAM as usize,
            Self::DeviceTreeError(_) => SBI_ERR_INVALID_PARAM as usize,

            Self::CannotStartNotStoppedHart() => SBI_ERR_ALREADY_AVAILABLE as usize,
            Self::CannotStopNotStartedHart() => SBI_ERR_ALREADY_AVAILABLE as usize,
            Self::CannotSuspedNotStartedHart() => SBI_ERR_ALREADY_AVAILABLE as usize,
            Self::CannotStartNotSuspendedHart() => SBI_ERR_ALREADY_AVAILABLE as usize,

            _ => SBI_ERR_FAILED as usize,
        }
    }
}
