// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use crate::error::TapError;
use alloc::vec::Vec;
use crate::spec::*;
use alloc::vec;
use crate::ensure;

pub struct AttestationPayloadParser {
    pub pointer: *const u8,
    pub size: usize,
}

impl AttestationPayloadParser {
    pub fn from_raw_pointer(pointer: *const u8, size: usize) -> Result<Self, TapError> {
        Ok(Self { pointer, size })
    }

    pub fn parse_and_verify(&mut self, decapsulation_key: &[u8]) -> Result<AttestationPayload, TapError> {
        ensure!(self.read_u32()? == ACE_MAGIC_TAP_START, TapError::InvalidMagicStart())?;
        self.read_u16()?;
        // if self.read_u16()? as usize != self.size {
        //     return Err(TapError::InvalidSize());
        // }
        let number_of_lockboxes = self.read_u16()?;
        ensure!(usize::from(number_of_lockboxes) <= MAX_NUMBER_OF_LOCKBOXES, TapError::InvalidSize())?;

        let mut symmetric_key = vec![];
        for _ in 0..number_of_lockboxes {
            let _size = self.read_u16()? as usize;
            // TODO: decide based on the lockbox name if this lockbox is intended for this device or not
            let _name = self.read_u64()?;
            let algorithm = LockboxAlgorithm::from_u16(self.read_u16()?)?;
            let esk_size = self.read_u16()? as usize;
            let esk = self.read_exact(esk_size)?;
            let nonce_size = self.read_u16()? as usize;
            let nonce = self.read_exact(nonce_size)?;
            let tag_size = self.read_u16()? as usize;
            let tag = self.read_exact(tag_size)?;
            let tsk_size = self.read_u16()? as usize;
            symmetric_key = self.read_exact(tsk_size)?;
            algorithm.decode(decapsulation_key, &esk, &nonce, &tag, &mut symmetric_key)?;
        }
        ensure!(!symmetric_key.is_empty(), TapError::NoLockboxFound())?;

        let payload_encryption_algorithm = PayloadEncryptionAlgorithm::from_u16(self.read_u16()?)?;
        match payload_encryption_algorithm {
            PayloadEncryptionAlgorithm::Debug => {},
            PayloadEncryptionAlgorithm::AesGcm256 => self.decrypt_aes_gcm_256(&symmetric_key)?,
        }

        let number_of_digests = self.read_u16()?;
        let mut digests = Vec::with_capacity(number_of_digests.into());
        for _ in 0..number_of_digests {
            let size = self.read_u16()? as usize;
            ensure!(size >= 4, TapError::InvalidSize())?;
            let pcr_id = self.read_u16()?;
            let algorithm = DigestAlgorithm::from_u16(self.read_u16()?)?;
            let value = self.read_exact(size-4)?;
            digests.push(Digest {
                pcr_id,
                algorithm,
                value
            });
        }

        let number_of_secrets = self.read_u16()?;
        let mut secrets = vec![];
        for _ in 0..number_of_secrets {
            let size = self.read_u16()? as usize;
            ensure!(size >= 10, TapError::InvalidSize())?;
            let name = self.read_u64()? as u64;
            let value = self.read_exact(size-10)?;
            secrets.push(Secret { name, value });
        }

        Ok(AttestationPayload { digests, secrets })
    }

    fn decrypt_aes_gcm_256(&mut self, symmetric_key: &[u8]) -> Result<(), TapError> {
        use aes_gcm::{AeadInPlace, Aes256Gcm, Key, KeyInit, Tag, Nonce};

        let nonce_size = self.read_u16()? as usize;
        let nonce = self.read_exact(nonce_size)?;
        let tag_size = self.read_u16()? as usize;
        let tag = self.read_exact(tag_size)?;
        let payload_size = self.read_u16()? as usize;

        ensure!(symmetric_key.len() == 32, TapError::InvalidTskSize())?;
        let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(symmetric_key));
        let nonce = Nonce::from_slice(&nonce);
        let tag = Tag::from_slice(&tag);
        let mut data_slice = unsafe{ core::slice::from_raw_parts_mut(self.pointer as *mut u8, payload_size) };
        cipher.decrypt_in_place_detached(nonce, b"", &mut data_slice, &tag)?;
        Ok(())
    }

    fn read_u16(&mut self) -> Result<u16, TapError> {
        let value = unsafe { (self.pointer as *const u16).read_volatile() };
        self.pointer = self.pointer.wrapping_add(2);
        Ok(value)
    }

    fn read_u32(&mut self) -> Result<u32, TapError> {
        let value = unsafe { (self.pointer as *const u32).read_volatile() };
        self.pointer = self.pointer.wrapping_add(4);
        Ok(value)
    }

    fn read_u64(&mut self) -> Result<u64, TapError> {
        let value = unsafe { (self.pointer as *const u64).read_volatile() };
        self.pointer = self.pointer.wrapping_add(8);
        Ok(value)
    }

    fn read_exact(&mut self, size: usize) -> Result<Vec<u8>, TapError> {
        let mut result = Vec::with_capacity(size);
        for _ in 0..size {
            let value = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
            result.push(value);
        }
        Ok(result)
    }
}