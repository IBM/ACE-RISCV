// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
pub use crate::error::TapError;
use crate::ensure;
use crate::spec::*;

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
        self.read_u16()?; // reserved / total-size field (ignored for now)
        let number_of_lockboxes = self.read_u16()?;
        ensure!(usize::from(number_of_lockboxes) <= MAX_NUMBER_OF_LOCKBOXES, TapError::TooManyLockboxes())?;

        let mut symmetric_key: heapless::Vec<u8, MAX_TSK_SIZE> = heapless::Vec::new();
        for _ in 0..number_of_lockboxes {
            let _size = self.read_u16()? as usize;
            let _name = self.read_u64()?;
            let algorithm = LockboxAlgorithm::from_u16(self.read_u16()?)?;

            let esk_size = self.read_u16()? as usize;
            ensure!(esk_size <= MAX_ESK_SIZE, TapError::ValueTooLarge())?;
            let esk_ptr = self.pointer;
            self.pointer = self.pointer.wrapping_add(esk_size);

            let nonce_size = self.read_u16()? as usize;
            ensure!(nonce_size <= MAX_NONCE_SIZE, TapError::ValueTooLarge())?;
            let nonce_buf = self.read_exact_n::<MAX_NONCE_SIZE>(nonce_size)?;

            let tag_size = self.read_u16()? as usize;
            ensure!(tag_size <= MAX_TAG_SIZE, TapError::ValueTooLarge())?;
            let tag_buf = self.read_exact_n::<MAX_TAG_SIZE>(tag_size)?;

            let tsk_size = self.read_u16()? as usize;
            ensure!(tsk_size <= MAX_TSK_SIZE, TapError::ValueTooLarge())?;
            symmetric_key.clear();
            let tsk_buf = self.read_exact_n::<MAX_TSK_SIZE>(tsk_size)?;
            symmetric_key.extend_from_slice(&tsk_buf).map_err(|_| TapError::ValueTooLarge())?;

            let esk: &[u8] = unsafe { core::slice::from_raw_parts(esk_ptr, esk_size) };
            ensure!(decapsulation_key.len() <= MAX_DK_SIZE, TapError::ValueTooLarge())?;
            algorithm.decode(decapsulation_key, esk, &nonce_buf, &tag_buf, &mut symmetric_key)?;
        }
        ensure!(!symmetric_key.is_empty(), TapError::NoLockboxFound())?;

        let payload_encryption_algorithm = PayloadEncryptionAlgorithm::from_u16(self.read_u16()?)?;
        match payload_encryption_algorithm {
            PayloadEncryptionAlgorithm::Debug => {}
            PayloadEncryptionAlgorithm::AesGcm256 => self.decrypt_aes_gcm_256(&symmetric_key)?,
        }

        let number_of_digests = self.read_u16()?;
        ensure!(usize::from(number_of_digests) <= MAX_NUMBER_OF_DIGESTS, TapError::TooManyDigests())?;
        let mut digests: heapless::Vec<Digest, MAX_NUMBER_OF_DIGESTS> = heapless::Vec::new();
        for _ in 0..number_of_digests {
            let size = self.read_u16()? as usize;
            ensure!(4 <= size, TapError::InvalidSize())?;
            let pcr_id = self.read_u16()?;
            let algorithm = DigestAlgorithm::from_u16(self.read_u16()?)?;
            let value_len = size - 4;
            ensure!(value_len <= MAX_DIGEST_VALUE_SIZE, TapError::ValueTooLarge())?;
            let value = self.read_exact_n::<MAX_DIGEST_VALUE_SIZE>(value_len)?;
            digests.push(Digest { pcr_id, algorithm, value }).map_err(|_| TapError::TooManyDigests())?;
        }

        let number_of_secrets = self.read_u16()?;
        ensure!(usize::from(number_of_secrets) <= MAX_NUMBER_OF_SECRETS, TapError::TooManySecrets())?;
        let mut secrets: heapless::Vec<Secret, MAX_NUMBER_OF_SECRETS> = heapless::Vec::new();
        for _ in 0..number_of_secrets {
            let size = self.read_u16()? as usize;
            ensure!(10 <= size, TapError::InvalidSize())?;
            let name = self.read_u64()?;
            let value_len = size - 10;
            ensure!(value_len <= MAX_SECRET_VALUE_SIZE, TapError::ValueTooLarge())?;
            let value = self.read_exact_n::<MAX_SECRET_VALUE_SIZE>(value_len)?;
            secrets.push(Secret { name, value }).map_err(|_| TapError::TooManySecrets())?;
        }

        Ok(AttestationPayload { digests, secrets })
    }

    fn decrypt_aes_gcm_256(&mut self, symmetric_key: &[u8]) -> Result<(), TapError> {
        use aes_gcm::{AeadInOut, Aes256Gcm, Key, KeyInit, Nonce, Tag};
        use aes_gcm::aead::inout::InOutBuf;

        let nonce_size = self.read_u16()? as usize;
        ensure!(nonce_size <= MAX_NONCE_SIZE, TapError::ValueTooLarge())?;
        let nonce_buf = self.read_exact_n::<MAX_NONCE_SIZE>(nonce_size)?;

        let tag_size = self.read_u16()? as usize;
        ensure!(tag_size <= MAX_TAG_SIZE, TapError::ValueTooLarge())?;
        let tag_buf = self.read_exact_n::<MAX_TAG_SIZE>(tag_size)?;

        let payload_size = self.read_u16()? as usize;
        ensure!(payload_size <= ACE_MAX_TAP_SIZE, TapError::InvalidSize())?;

        ensure!(symmetric_key.len() == 32, TapError::InvalidTskSize())?;
        let cipher = Aes256Gcm::new(&Key::<Aes256Gcm>::try_from(symmetric_key)?);
        let nonce = Nonce::try_from(nonce_buf.as_slice())?;
        let tag = Tag::try_from(tag_buf.as_slice())?;
        let data_slice = unsafe { core::slice::from_raw_parts_mut(self.pointer as *mut u8, payload_size) };
        cipher.decrypt_inout_detached(&nonce, b"", InOutBuf::from(data_slice), &tag)?;
        Ok(())
    }

    fn read_u16(&mut self) -> Result<u16, TapError> {
        let mut buf = [0u8; 2];
        for b in buf.iter_mut() {
            *b = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
        }
        Ok(u16::from_le_bytes(buf))
    }

    fn read_u32(&mut self) -> Result<u32, TapError> {
        let mut buf = [0u8; 4];
        for b in buf.iter_mut() {
            *b = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
        }
        Ok(u32::from_le_bytes(buf))
    }

    fn read_u64(&mut self) -> Result<u64, TapError> {
        let mut buf = [0u8; 8];
        for b in buf.iter_mut() {
            *b = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
        }
        Ok(u64::from_le_bytes(buf))
    }

    fn read_exact_n<const N: usize>(&mut self, size: usize) -> Result<heapless::Vec<u8, N>, TapError> {
        ensure!(size <= N, TapError::ValueTooLarge())?;
        let mut result: heapless::Vec<u8, N> = heapless::Vec::new();
        for _ in 0..size {
            let byte = unsafe { self.pointer.read_volatile() };
            self.pointer = self.pointer.wrapping_add(1);
            result.push(byte).map_err(|_| TapError::ValueTooLarge())?;
        }
        Ok(result)
    }
}
