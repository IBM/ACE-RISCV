// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

pub use crate::error::TapError;
use alloc::vec::Vec;
use alloc::vec;
use crate::spec::*;

pub struct TeeAttestationPayloadParser {
    pub pointer: *const u8,
    pub size: usize,
}

impl TeeAttestationPayloadParser {
    pub fn from_raw_pointer(pointer: *const u8, size: usize) -> Result<Self, TapError> {
        Ok(Self {
            pointer, size
        })
    }

    pub fn parse_and_verify(&mut self) -> Result<TeeAttestationPayload, TapError> {
        if self.read_u16()? != ACE_MAGIC_TAP_START {
            return Err(TapError::InvalidMagicStart());
        }
        self.read_u16()?;
        // if self.read_u16()? as usize != self.size {
        //     return Err(TapError::InvalidSize());
        // }
        let number_of_lockboxes = self.read_u16()?;
        let mut lockboxes = vec![];
        for _ in 0..number_of_lockboxes {
            let size = self.read_u16()? as usize;
            let name = self.read_u64()?;
            let algorithm = TapLockboxAlgorithm::from_u16(self.read_u16()?)?;
            let value = self.read_exact(size-10)?;
            lockboxes.push(Lockbox {
                name,
                algorithm,
                value
            });
        }
        // TODO: recover symmetric key
        let symmetric_key = [0u8; 32];

        let payload_encryption_algorithm = TapPayloadEncryptionAlgorithm::from_u16(self.read_u16()?)?;
        match payload_encryption_algorithm {
            TapPayloadEncryptionAlgorithm::Debug => {},
            TapPayloadEncryptionAlgorithm::AesGcm256 => self.decrypt_aes_gcm_256(symmetric_key)?,
        }

        let number_of_digests = self.read_u16()?;
        let mut digests = vec![];
        for _ in 0..number_of_digests {
            let size = self.read_u16()? as usize;
            let entry_type = TapDigestEntryType::from_u16(self.read_u16()?)?;
            let algorithm = TapDigestAlgorithm::from_u16(self.read_u16()?)?;
            let value = self.read_exact(size-4)?;
            digests.push(TapDigest {
                entry_type,
                algorithm,
                value
            });
        }

        let number_of_secrets = self.read_u16()?;
        let mut secrets = vec![];
        for _ in 0..number_of_secrets {
            let size = self.read_u16()? as usize;
            let name = self.read_u64()? as u64;
            let value = self.read_exact(size-10)?;
            secrets.push(TapSecret { name, value });
        }

        Ok(TeeAttestationPayload {
            lockboxes,
            digests,
            secrets,
        })
    }

    fn decrypt_aes_gcm_256(&mut self, symmetric_key: [u8; 32]) -> Result<(), TapError> {
        use aes_gcm::{AeadInPlace, Aes256Gcm, Key, KeyInit, Tag, Nonce};

        let nonce_size = self.read_u16()? as usize;
        let nonce = self.read_exact(nonce_size)?;
        let tag_size = self.read_u16()? as usize;
        let tag = self.read_exact(tag_size)?;
        let payload_size = self.read_u16()? as usize;

        let key: Key<Aes256Gcm> = symmetric_key.into();
        let cipher = Aes256Gcm::new(&key);
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

    fn read_u64(&mut self) -> Result<u64, TapError> {
        let value = unsafe { (self.pointer as *const u64).read_volatile() };
        self.pointer = self.pointer.wrapping_add(8);
        Ok(value)
    }

    fn read_exact(&mut self, size: usize) -> Result<Vec<u8>, TapError> {
        let mut result = vec![];
        for _ in 0..size {
            let value = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
            result.push(value);
        }
        Ok(result)
    }
}