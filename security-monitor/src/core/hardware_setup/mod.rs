// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

use crate::core::architecture::riscv::ReadWriteRiscvCsr;
use crate::core::architecture::riscv::specification::*;
use crate::core::architecture::{CSR, HardwareExtension};
use crate::error::Error;
use alloc::vec::Vec;
use spin::{Once, RwLock, RwLockReadGuard, RwLockWriteGuard};

static HARDWARE_SETUP: Once<RwLock<HardwareSetup>> = Once::new();

pub struct HardwareSetup {
    isa_extensions: Vec<HardwareExtension>,
    vector_vlenb: Option<usize>,
}

impl HardwareSetup {
    const NOT_INITIALIZED: &'static str = "Bug: Hardware configuration setup not initialized";

    const REQUIRED_BASE_EXTENSIONS: &'static [&'static str] = &[ATOMIC_EXTENSION, HYPERVISOR_EXTENSION];

    const REQUIRED_EXTENSIONS: &'static [&'static str] = &[SSTC_EXTENSION, IFENCEI_EXTENSION];

    pub fn initialize() -> Result<(), Error> {
        let hardware_setup = Self { isa_extensions: Vec::new(), vector_vlenb: None };

        ensure_not!(HARDWARE_SETUP.is_completed(), Error::Reinitialization())?;

        HARDWARE_SETUP.call_once(|| RwLock::new(hardware_setup));
        Ok(())
    }

    pub fn check_isa_extensions(prop: &str) -> Result<(), Error> {
        debug!("{}", prop);

        ensure!(prop.starts_with(RISCV_ARCH), Error::InvalidCpuArch())?;

        let extensions = &prop.split('_').collect::<Vec<&str>>();

        Self::REQUIRED_BASE_EXTENSIONS
            .into_iter()
            .try_for_each(|ext| ensure!(extensions[0].contains(*ext), Error::MissingCpuExtension()))?;

        Self::REQUIRED_EXTENSIONS.into_iter().try_for_each(|ext| ensure!(extensions.contains(ext), Error::MissingCpuExtension()))?;

        Ok(())
    }

    pub fn add_extension(extension: HardwareExtension) -> Result<(), Error> {
        Self::try_write(|hardware_setup| Ok(hardware_setup.isa_extensions.push(extension)))
    }

    pub fn is_extension_supported(extension: HardwareExtension) -> bool {
        Self::try_read(|hardware_setup| Ok(hardware_setup.isa_extensions.contains(&extension))).unwrap_or(false)
    }

    pub fn vector_vlenb() -> Result<usize, Error> {
        Self::try_read(|hardware_setup| {
            if !hardware_setup.isa_extensions.contains(&HardwareExtension::VectorExtension) {
                return Ok(0);
            }

            hardware_setup.vector_vlenb.ok_or(Error::InvalidVectorRegisterSize())
        })
    }

    pub fn validate_vector_vlenb() -> Result<(), Error> {
        if !Self::is_extension_supported(HardwareExtension::VectorExtension) {
            return Ok(());
        }

        let old_mstatus = CSR.mstatus.read_and_set_bits(SR_VS_DIRTY);

        let vlenb = ReadWriteRiscvCsr::<CSR_VLENB>::new().read();

        CSR.mstatus.write(old_mstatus);

        if !vlenb.is_power_of_two() || vlenb > 8192 {
            return Err(Error::InvalidVectorRegisterSize());
        }

        Self::try_write(|hardware_setup| match hardware_setup.vector_vlenb {
            None => {
                hardware_setup.vector_vlenb = Some(vlenb);
                Ok(())
            }
            Some(expected) if expected == vlenb => Ok(()),
            Some(_) => Err(Error::InvalidVectorRegisterSize()),
        })
    }

    fn try_read<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&RwLockReadGuard<'_, Self>) -> Result<F, Error> {
        op(&HARDWARE_SETUP.get().expect(Self::NOT_INITIALIZED).read())
    }

    fn try_write<F, O>(op: O) -> Result<F, Error>
    where O: FnOnce(&mut RwLockWriteGuard<'static, Self>) -> Result<F, Error> {
        op(&mut HARDWARE_SETUP.get().expect(Self::NOT_INITIALIZED).write())
    }
}
