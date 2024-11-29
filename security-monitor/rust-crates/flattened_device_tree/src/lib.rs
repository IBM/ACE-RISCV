// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
#![no_std]
#![no_main]

use fdt_rs::base::DevTree;
use fdt_rs::prelude::{FallibleIterator, PropReader};
use fdt_rs::base::DevTreeNode;
use crate::FdtError::FdtPointerNotAligned;
use core::mem::align_of;

pub use crate::error::FdtError;

mod error;

/// This is a wrapper over a third party library that parses the flattened device tree (FDT).
pub struct FlattenedDeviceTree<'a> {
    inner: DevTree<'a>
}

impl<'a> FlattenedDeviceTree<'a> {
    pub const FDT_HEADER_SIZE: usize = 40;

    /// Creates an instance of a wrapper over the library that parses the flattened device tree (FDT). Returns error if address is not a 8-bytes aligned pointer to the valid flattened device tree (FDT).
    ///
    /// # Safety
    ///
    /// Caller must guarantee that:
    ///   * the length of the pointed buffer is at least `DevTree::MIN_HEADER_SIZE`
    pub unsafe fn from_raw_pointer(address: *const u8) -> Result<Self, FdtError> {
        if address.align_offset(align_of::<u64>()) != 0 {
            return Err(FdtPointerNotAligned());
        }
        Ok(Self { inner: unsafe { DevTree::from_raw_pointer(address)? } })
    }

    pub unsafe fn total_size(address: *const u8) -> Result<usize, FdtError> {
        // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be within the
        // page boundary. These 8 bytes should contain the `FDT magic` (first 4 bytes) and `FDT totalsize` (next 4 bytes).
        if address.align_offset(align_of::<u64>()) != 0 {
            return Err(FdtPointerNotAligned());
        }
        let magic_and_size: u64 = unsafe { (address as *const u64).read_volatile() };
        let fdt_total_size: usize = u32::from_be((magic_and_size >> 32) as u32) as usize;
        Ok(fdt_total_size)
    }

    pub fn harts<'b>(&'b self) -> impl Iterator<Item = Hart<'b, 'a>> {
        self.inner
            .nodes()
            .filter(|n| {
                n.props()
                    .any(|p| Ok(p.name()? == "device_type" && p.str()? == "cpu"))
            })
            .iterator()
            .filter_map(|n| Some(Hart { inner: n.ok()? }))
    }

    pub fn memory(&self) -> Result<FdtMemoryRegion, FdtError>  {
        let mem_prop = self.inner.props()
            .find(|p| Ok(p.name()? == "device_type" && p.str()? == "memory"))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        let reg_prop = mem_prop.node()
            .props()
            .find(|p| Ok(p.name().unwrap_or("empty") == "reg"))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        Ok(FdtMemoryRegion { base: reg_prop.u64(0)?, size: reg_prop.u64(1)? })
    }

    pub fn initrd(&self) -> Result<(usize, usize), FdtError>  {
        let initrd_start_prop = self.inner.props()
            .find(|p| Ok(p.name()?.starts_with("linux,initrd-start")))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        let initrd_end_prop = self.inner.props()
            .find(|p| Ok(p.name()?.starts_with("linux,initrd-end")))?
            .ok_or_else(|| FdtError::NoMemoryNode())?;

        Ok((initrd_start_prop.u64(0)? as usize, initrd_end_prop.u64(0)? as usize ))
    }
}

#[derive(Copy, Clone, Debug, Default)]
pub struct FdtMemoryRegion {
    pub base: u64,
    pub size: u64,
}

impl FdtMemoryRegion {
    pub fn into_range(&self) -> Result<(usize, usize), FdtError> {
        Ok((usize::try_from(self.base)?, usize::try_from(self.base.checked_add(self.size).ok_or(FdtError::FdtInvalidIntegerValue())?)?))
    }
}

#[derive(Clone)]
pub struct Hart<'a, 'dt> {
    inner: DevTreeNode<'a, 'dt>,
}

impl<'a, 'dt> Hart<'a, 'dt> {
    pub fn hart_id(&self) -> Option<u64> {
        let prop = self.inner.props().find(|p| Ok(p.name()? == "reg")).ok()??;
        Some(prop.u32(0).ok()? as u64)
    }

    pub fn property_str(&self, name: &str) -> Option<&str> {
        let prop = self.inner.props().find(|p| Ok(p.name()? == name)).ok()??;
        let value = core::str::from_utf8(prop.propbuf()).ok().and_then(|v| v.strip_suffix('\0'))?;
        Some(value)
    }

}