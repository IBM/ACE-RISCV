// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use heapless::Vec;

pub const ACE_HEADER_SIZE: usize = 8;
pub const ACE_FOOTER_SIZE: usize = 8;
pub const ACE_MAGIC_TAP_START: u32 = 0xACE0ACE0;
pub const ACE_MAGIC_TAP_END: u32 = 0xACE1ACE1;
/// Maximum total wire size of a TAP blob (one 4 KiB page).
pub const ACE_MAX_TAP_SIZE: usize = 4096;

/// Maximum number of lockboxes (key-encapsulations) in one TAP.
/// Each lockbox targets one device identity; 16 is more than enough for any
/// realistic deployment while keeping the parser's stack budget bounded.
pub const MAX_NUMBER_OF_LOCKBOXES: usize = 16;

/// Maximum number of measurement digests (PCR values) in one TAP.
/// CoVE defines at most 24 PCR slots; we round up to 32 for headroom.
pub const MAX_NUMBER_OF_DIGESTS: usize = 32;

/// Maximum number of secrets carried in one TAP.
/// A VM rarely needs more than a handful of symmetric keys at provisioning.
pub const MAX_NUMBER_OF_SECRETS: usize = 8;

/// Maximum byte length of a single secret value.
/// 256 bytes covers all standard symmetric key material:
///   AES-256 (32 B), HMAC-SHA-512 key (64 B), two AES keys + nonce (76 B), etc.
pub const MAX_SECRET_VALUE_SIZE: usize = 256;

/// Maximum byte length of a single digest value.
/// SHA-512 produces 64 bytes; 128 bytes gives comfortable headroom.
pub const MAX_DIGEST_VALUE_SIZE: usize = 128;

/// Maximum size of the encapsulated symmetric key (esk).
/// ML-KEM-1024 ciphertext is exactly 1568 bytes (FIPS 203, K=4, Du=11, Dv=5:
///   32*(Du*K + Dv) = 32*49 = 1568).
pub const MAX_ESK_SIZE: usize = 1568;

/// Maximum size of an AES-GCM nonce.
/// AES-256-GCM uses a 96-bit (12-byte) nonce.
pub const MAX_NONCE_SIZE: usize = 12;

/// Maximum size of an AES-GCM authentication tag.
/// AES-256-GCM produces a 128-bit (16-byte) tag.
pub const MAX_TAG_SIZE: usize = 16;

/// Maximum size of the transport symmetric key (tsk) stored in a Lockbox.
/// Reuses MAX_SECRET_VALUE_SIZE: the tsk is used to decrypt the payload that
/// carries the secrets, so it must fit within the same bound.
pub const MAX_TSK_SIZE: usize = MAX_SECRET_VALUE_SIZE;

/// Maximum size of the ML-KEM-1024 decapsulation key accepted by the parser.
/// FIPS 203: dk size = 768*K + 96 = 768*4 + 96 = 3168 bytes.
pub const MAX_DK_SIZE: usize = 3168;

pub struct AttestationPayload {
    pub digests: Vec<Digest, MAX_NUMBER_OF_DIGESTS>,
    pub secrets: Vec<Secret, MAX_NUMBER_OF_SECRETS>,
}

pub struct Lockbox {
    pub name: u64,
    pub algorithm: LockboxAlgorithm,
    pub esk: Vec<u8, MAX_ESK_SIZE>,
    pub nonce: Vec<u8, MAX_NONCE_SIZE>,
    pub tag: Vec<u8, MAX_TAG_SIZE>,
    pub tsk: Vec<u8, MAX_TSK_SIZE>,
}

impl Lockbox {
    #[cfg(feature = "serializer")]
    pub fn new(
        lockbox_algorithm: LockboxAlgorithm,
        encapsulation_key: &[u8],
        tsk: &mut Vec<u8, MAX_TSK_SIZE>,
    ) -> Result<Self, TapError> {
        let (esk, nonce, tag, tsk) = lockbox_algorithm.encode(encapsulation_key, tsk)?;
        Ok(Self { name: 0, algorithm: lockbox_algorithm, esk, nonce, tag, tsk })
    }
}

#[repr(u16)]
#[derive(Debug, Clone, Copy)]
pub enum LockboxAlgorithm {
    Debug = 0,
    MlKem1024Aes256 = 1,
}

impl LockboxAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::MlKem1024Aes256),
            v => Err(TapError::UnsupportedLockboxAlgorithm(v)),
        }
    }

    #[cfg(feature = "serializer")]
    pub fn encode(
        &self,
        encapsulation_key: &[u8],
        tsk: &mut Vec<u8, MAX_TSK_SIZE>,
    ) -> Result<(
        Vec<u8, MAX_ESK_SIZE>,
        Vec<u8, MAX_NONCE_SIZE>,
        Vec<u8, MAX_TAG_SIZE>,
        Vec<u8, MAX_TSK_SIZE>,
    ), TapError> {
        match self {
            LockboxAlgorithm::Debug => {
                // Debug mode: all fields empty, tsk is passed through unchanged.
                Ok((Vec::new(), Vec::new(), Vec::new(), Vec::new()))
            }
            LockboxAlgorithm::MlKem1024Aes256 => {
                use rand::Rng;
                let mut rng = rand::thread_rng();
                use ml_kem::{B32, ml_kem_1024::EncapsulationKey, kem::Key as KemKey};

                let ek_key_arr = KemKey::<EncapsulationKey>::try_from(encapsulation_key)
                    .map_err(|_| TapError::KemError())?;
                let ek = EncapsulationKey::new(&ek_key_arr).map_err(|_| TapError::KemError())?;
                let mut m_bytes = [0u8; 32];
                rng.fill(&mut m_bytes);
                let m = B32::try_from(m_bytes.as_slice()).map_err(|_| TapError::KemError())?;
                let (esk_arr, aes_key) = ek.encapsulate_deterministic(&m);

                use aes_gcm::{AeadInOut, Aes256Gcm, Key, KeyInit};
                use aes_gcm::aead::inout::InOutBuf;
                let mut nonce_bytes = [0u8; MAX_NONCE_SIZE];
                rng.fill(&mut nonce_bytes);
                let key: &Key<Aes256Gcm> = &Key::<Aes256Gcm>::try_from(aes_key.as_slice())?;
                let cipher = Aes256Gcm::new(key);
                let nonce = aes_gcm::Nonce::try_from(nonce_bytes.as_slice())?;
                let tag_arr = cipher.encrypt_inout_detached(&nonce, b"", InOutBuf::from(tsk.as_mut_slice()))?;

                let mut esk: Vec<u8, MAX_ESK_SIZE> = Vec::new();
                esk.extend_from_slice(esk_arr.as_slice()).map_err(|_| TapError::ValueTooLarge())?;
                let mut nonce_out: Vec<u8, MAX_NONCE_SIZE> = Vec::new();
                nonce_out.extend_from_slice(nonce.as_slice()).map_err(|_| TapError::ValueTooLarge())?;
                let mut tag_out: Vec<u8, MAX_TAG_SIZE> = Vec::new();
                tag_out.extend_from_slice(tag_arr.as_slice()).map_err(|_| TapError::ValueTooLarge())?;
                let mut tsk_out: Vec<u8, MAX_TSK_SIZE> = Vec::new();
                tsk_out.extend_from_slice(tsk.as_slice()).map_err(|_| TapError::ValueTooLarge())?;

                Ok((esk, nonce_out, tag_out, tsk_out))
            }
        }
    }

    #[cfg(feature = "parser")]
    pub fn decode(
        &self, decapsulation_key: &[u8], esk: &[u8], nonce: &[u8], tag: &[u8],
        tsk: &mut Vec<u8, MAX_TSK_SIZE>,
    ) -> Result<(), TapError> {
        match self {
            LockboxAlgorithm::Debug => Ok(()),
            LockboxAlgorithm::MlKem1024Aes256 => {
                use aes_gcm::{AeadInOut, Aes256Gcm, Key, KeyInit, Nonce, Tag};
                use aes_gcm::aead::inout::InOutBuf;
                use ml_kem::{
                    ml_kem_1024::{Ciphertext, DecapsulationKey},
                    kem::Decapsulate,
                    ExpandedDecapsulationKey,
                };

                let ct_arr = Ciphertext::try_from(esk).map_err(|_| TapError::KemError())?;
                let dk_expanded = ExpandedDecapsulationKey::<ml_kem::MlKem1024>::try_from(decapsulation_key)
                    .map_err(|_| TapError::KemError())?;
                // `from_expanded` is the correct API for loading a pre-existing 3168-byte key;
                // the deprecation warning points at `from_seed` which takes a 64-byte random seed
                // and is not equivalent. Suppress until ml-kem stabilises a replacement.
                #[allow(deprecated)]
                let dk = DecapsulationKey::from_expanded(&dk_expanded).map_err(|_| TapError::KemError())?;
                let sk = dk.decapsulate(&ct_arr);

                let cipher = Aes256Gcm::new(&Key::<Aes256Gcm>::try_from(sk.as_slice())?);
                cipher
                    .decrypt_inout_detached(
                        &Nonce::try_from(nonce)?,
                        b"",
                        InOutBuf::from(tsk.as_mut_slice()),
                        &Tag::try_from(tag)?,
                    )
                    .unwrap();
                Ok(())
            }
        }
    }
}

pub struct Digest {
    pub pcr_id: u16,
    pub algorithm: DigestAlgorithm,
    pub value: Vec<u8, MAX_DIGEST_VALUE_SIZE>,
}

impl Digest {
    pub fn value_in_hex(&self) -> alloc::string::String {
        use crate::alloc::string::ToString;
        self.value
            .iter()
            .map(|b| alloc::format!("{:02x}", b).to_string())
            .collect::<alloc::vec::Vec<alloc::string::String>>()
            .join("")
    }

    pub fn pcr_id(&self) -> u16 {
        self.pcr_id
    }
}

#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigestAlgorithm {
    Debug = 0,
    Sha512 = 1,
}

impl DigestAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::Sha512),
            v => Err(TapError::UnsupportedDigestAlgorithm(v)),
        }
    }

    pub fn digest_size(&self) -> u16 {
        match self {
            Self::Debug => 0,
            Self::Sha512 => 512 / 8,
        }
    }
}

pub struct Secret {
    pub name: u64,
    pub value: Vec<u8, MAX_SECRET_VALUE_SIZE>,
}

#[repr(u16)]
#[derive(Debug, Clone, Copy)]
pub enum PayloadEncryptionAlgorithm {
    Debug = 0,
    AesGcm256 = 1,
}

impl PayloadEncryptionAlgorithm {
    pub fn from_u16(value: u16) -> Result<Self, TapError> {
        match value {
            0 => Ok(Self::Debug),
            1 => Ok(Self::AesGcm256),
            v => Err(TapError::UnsupportedPayloadEncryptionAlgorithm(v)),
        }
    }
}
