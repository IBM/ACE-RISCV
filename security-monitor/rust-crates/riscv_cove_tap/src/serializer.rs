// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use crate::spec::*;
use heapless::Vec;

/// Type alias for a bounded wire output buffer sized to the maximum TAP blob.
type WireBuffer = Vec<u8, ACE_MAX_TAP_SIZE>;

#[inline]
fn push_u16(buf: &mut WireBuffer, value: u16) -> Result<(), TapError> {
    buf.extend_from_slice(&value.to_le_bytes()).map_err(|_| TapError::InvalidSize())
}

#[inline]
fn push_u32(buf: &mut WireBuffer, value: u32) -> Result<(), TapError> {
    buf.extend_from_slice(&value.to_le_bytes()).map_err(|_| TapError::InvalidSize())
}

#[inline]
fn push_u64(buf: &mut WireBuffer, value: u64) -> Result<(), TapError> {
    buf.extend_from_slice(&value.to_le_bytes()).map_err(|_| TapError::InvalidSize())
}

#[inline]
fn push_bytes(buf: &mut WireBuffer, bytes: &[u8]) -> Result<(), TapError> {
    buf.extend_from_slice(bytes).map_err(|_| TapError::InvalidSize())
}

pub struct AttestationPayloadSerializer {}

impl AttestationPayloadSerializer {
    pub fn new() -> Self {
        Self {}
    }

    pub fn serialize(&self, lockboxes: Vec<Lockbox, MAX_NUMBER_OF_LOCKBOXES>, mut payload: AttestationPayload, tsk: &[u8]) -> Result<WireBuffer, TapError> {
        let digests = self.serialize_digests(&mut payload)?;
        let secrets = self.serialize_secrets(&mut payload)?;
        let mut encrypted_part = self.encrypt_aes_gcm_256(digests, secrets, tsk)?;
        let mut lockboxes = self.serialize_lockboxes(lockboxes)?;

        let total_size = lockboxes.len() + encrypted_part.len();

        let mut result = WireBuffer::new();
        push_u32(&mut result, ACE_MAGIC_TAP_START)?;
        push_u16(&mut result, total_size as u16)?;
        result.extend_from_slice(&lockboxes).map_err(|_| TapError::InvalidSize())?;
        result.extend_from_slice(&encrypted_part).map_err(|_| TapError::InvalidSize())?;

        Ok(result)
    }

    fn serialize_lockboxes(&self, lockboxes: Vec<Lockbox, MAX_NUMBER_OF_LOCKBOXES>) -> Result<WireBuffer, TapError> {
        let mut result = WireBuffer::new();
        push_u16(&mut result, lockboxes.len() as u16)?;
        for lockbox in lockboxes.into_iter() {
            let entry_size = lockbox.esk.len() + lockbox.nonce.len() + lockbox.tag.len() + lockbox.tsk.len() + 18;
            push_u16(&mut result, entry_size as u16)?;
            push_u64(&mut result, lockbox.name)?;
            push_u16(&mut result, lockbox.algorithm as u16)?;
            push_u16(&mut result, lockbox.esk.len() as u16)?;
            push_bytes(&mut result, &lockbox.esk)?;
            push_u16(&mut result, lockbox.nonce.len() as u16)?;
            push_bytes(&mut result, &lockbox.nonce)?;
            push_u16(&mut result, lockbox.tag.len() as u16)?;
            push_bytes(&mut result, &lockbox.tag)?;
            push_u16(&mut result, lockbox.tsk.len() as u16)?;
            push_bytes(&mut result, &lockbox.tsk)?;
        }
        Ok(result)
    }

    fn serialize_digests(&self, payload: &AttestationPayload) -> Result<WireBuffer, TapError> {
        let mut result = WireBuffer::new();
        push_u16(&mut result, payload.digests.len() as u16)?;
        for digest in payload.digests.iter() {
            let entry_size = digest.value.len() + 2 + 2;
            push_u16(&mut result, entry_size as u16)?;
            push_u16(&mut result, digest.pcr_id)?;
            push_u16(&mut result, digest.algorithm as u16)?;
            push_bytes(&mut result, &digest.value)?;
        }
        Ok(result)
    }

    fn serialize_secrets(&self, payload: &AttestationPayload) -> Result<WireBuffer, TapError> {
        let mut result = WireBuffer::new();
        push_u16(&mut result, payload.secrets.len() as u16)?;
        for secret in payload.secrets.iter() {
            let entry_size = secret.value.len() + 10;
            push_u16(&mut result, entry_size as u16)?;
            push_u64(&mut result, secret.name)?;
            push_bytes(&mut result, &secret.value)?;
        }
        Ok(result)
    }

    fn encrypt_aes_gcm_256(
        &self,
        digests: WireBuffer,
        secrets: WireBuffer,
        tsk: &[u8]
    ) -> Result<WireBuffer, TapError> {
        use aes_gcm::{AeadInOut, Aes256Gcm, Key, KeyInit};
        use aes_gcm::aead::inout::InOutBuf;
        use rand::RngExt;

        let mut plaintext = WireBuffer::new();
        push_bytes(&mut plaintext, &digests)?;
        push_bytes(&mut plaintext, &secrets)?;

        let key = Key::<Aes256Gcm>::try_from(tsk)?;
        let cipher = Aes256Gcm::new(&key);
        let mut nonce_bytes = [0u8; 12];
        let mut rng = rand::rng();
        rng.fill(&mut nonce_bytes);
        let nonce = aes_gcm::Nonce::try_from(nonce_bytes.as_slice())?;
        let tag = cipher
            .encrypt_inout_detached(&nonce, b"", InOutBuf::from(plaintext.as_mut_slice()))
            .map_err(|_| TapError::KemError())?;

        let mut result = WireBuffer::new();
        push_u16(&mut result, PayloadEncryptionAlgorithm::AesGcm256 as u16)?;
        push_u16(&mut result, nonce_bytes.len() as u16)?;
        push_bytes(&mut result, &nonce_bytes)?;
        push_u16(&mut result, tag.as_slice().len() as u16)?;
        push_bytes(&mut result, tag.as_slice())?;
        push_u16(&mut result, plaintext.len() as u16)?;
        push_bytes(&mut result, &plaintext)?;

        Ok(result)
    }
}
