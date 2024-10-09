// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use alloc::vec;
use crate::spec::*;
use alloc::vec::Vec;

pub struct AttestationPayloadSerializer {

}

impl AttestationPayloadSerializer {
    pub fn new() -> Self {
        Self {}
    }

    pub fn serialize(&self, mut payload: AttestationPayload) -> Result<Vec<u8>, TapError> {
        let digests = self.serialize_digests(&mut payload)?;
        let secrets = self.serialize_secrets(&mut payload)?;
        let mut encrypted_part = self.encrypt_aes_gcm_256(digests, secrets)?;
        let mut lockboxes = self.serialize_lockboxes(&mut payload)?;

        let total_size = lockboxes.len() + encrypted_part.len();

        let mut result = vec![];
        result.append(&mut ACE_MAGIC_TAP_START.to_le_bytes().to_vec());
        result.append(&mut (total_size as u16).to_le_bytes().to_vec());
        result.append(&mut lockboxes);
        result.append(&mut encrypted_part);
        // result.append(&mut ACE_MAGIC_TAP_END.to_le_bytes().to_vec());
        // result.append(&mut ((total_size + ACE_HEADER_SIZE) as u16).to_le_bytes().to_vec());

        Ok(result)
    }

    fn serialize_lockboxes(&self, payload: &mut AttestationPayload) -> Result<Vec<u8>, TapError> {
        // TODO: sanity check: lockboxes < 1024
        let mut result = vec![];
        result.append(&mut (payload.lockboxes.len() as u16).to_le_bytes().to_vec());
        for mut lockbox in payload.lockboxes.drain(..) {
            let entry_size = lockbox.value.len() + 10;
            result.append(&mut (entry_size as u16).to_le_bytes().to_vec());
            result.append(&mut (lockbox.name as u64).to_le_bytes().to_vec());
            result.append(&mut (lockbox.algorithm as u16).to_le_bytes().to_vec());
            result.append(&mut lockbox.value);
        }
        Ok(result)
    }

    fn serialize_digests(&self, payload: &mut AttestationPayload) -> Result<Vec<u8>, TapError> {
        // TODO: sanity check: digests < 1024
        let mut result = vec![];
        result.append(&mut (payload.digests.len() as u16).to_le_bytes().to_vec());
        for mut digest in payload.digests.drain(..) {
            let entry_size = digest.value.len() + 2 + 2;
            result.append(&mut (entry_size as u16).to_le_bytes().to_vec());
            result.append(&mut (digest.pcr_id).to_le_bytes().to_vec());
            result.append(&mut (digest.algorithm as u16).to_le_bytes().to_vec());
            result.append(&mut digest.value);
        }
        Ok(result)
    }

    fn serialize_secrets(&self, payload: &mut AttestationPayload) -> Result<Vec<u8>, TapError> {
        // TODO: sanity check: secrets < 1024
        let mut result = vec![];
        result.append(&mut (payload.secrets.len() as u16).to_le_bytes().to_vec());
        for mut secret in payload.secrets.drain(..) {
            let entry_size = secret.value.len() + 10;
            result.append(&mut (entry_size as u16).to_le_bytes().to_vec());
            result.append(&mut (secret.name).to_le_bytes().to_vec());
            result.append(&mut secret.value);
        }
        Ok(result)
    }

    fn encrypt_aes_gcm_256(&self, mut digests: Vec<u8>, mut secrets: Vec<u8>) -> Result<Vec<u8>, TapError> {
        use aes_gcm::{AeadInPlace, Aes256Gcm, Key, KeyInit};
        // use rand::rngs::OsRng;

        let mut encrypted_part = vec![];
        encrypted_part.append(&mut digests);
        encrypted_part.append(&mut secrets);

        let symmetric_key = [0u8; 32];
        // rand::thread_rng().fill_bytes(&mut symmetric_key);

        let key: Key<Aes256Gcm> = symmetric_key.into();
        let cipher = Aes256Gcm::new(&key);
        let nonce = [0u8; 12];
        // let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
        let nonce = aes_gcm::Nonce::from_slice(&nonce);
        let tag = cipher
            .encrypt_in_place_detached(&nonce, b"", &mut encrypted_part)
            .unwrap();

        let mut result = vec![];
        result.append(&mut (PayloadEncryptionAlgorithm::AesGcm256 as u16).to_le_bytes().to_vec());
        result.append(&mut (nonce.as_slice().len() as u16).to_le_bytes().to_vec());
        result.append(&mut nonce.as_slice().to_vec());
        result.append(&mut (tag.as_slice().len() as u16).to_le_bytes().to_vec());
        result.append(&mut tag.as_slice().to_vec());
        result.append(&mut (encrypted_part.len() as u16).to_le_bytes().to_vec());
        result.append(&mut encrypted_part);

        Ok(result)
    }

    // fn encrypt_rsa_2048_sha256_oasp(value: &[u8], public_key_file: String) -> Result<Vec<u8>, Error> {
    //     use rsa::pkcs1::DecodeRsaPublicKey;
    //     let public_key_pem: Vec<u8> = std::fs::read(public_key_file.clone())
    //         .map_err(|_| Error::CannotOpenFile(public_key_file))?;
    //     let public_key = rsa::RsaPublicKey::from_pkcs1_pem(&String::from_utf8_lossy(&public_key_pem))?;
    //     let padding = rsa::Oaep::new::<sha2::Sha256>();
    //     let encrypted_data = public_key.encrypt(&mut rand::thread_rng(), padding, value)?;
    //     Ok(encrypted_data)
    // }
}