// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::error::TapError;
use alloc::vec::Vec;

pub const ACE_HEADER_SIZE: usize = 8;
pub const ACE_FOOTER_SIZE: usize = 8;
pub const ACE_MAGIC_TAP_START: u32 = 0xACE0ACE0;
pub const ACE_MAGIC_TAP_END: u32 = 0xACE1ACE1;
pub const ACE_MAX_TAP_SIZE: usize = 4096; // size of the 4KiB page
pub const MAX_NUMBER_OF_LOCKBOXES: usize = 1024;

pub struct AttestationPayload {
    pub digests: Vec<Digest>,
    pub secrets: Vec<Secret>,
}

pub struct Lockbox {
    pub name: u64,
    pub algorithm: LockboxAlgorithm,
    pub esk: Vec<u8>,
    pub nonce: Vec<u8>,
    pub tag: Vec<u8>,
    pub tsk: Vec<u8>
}

impl Lockbox {
    #[cfg(feature = "serializer")]
    pub fn new(lockbox_algorithm: LockboxAlgorithm, encapsulation_key: &Vec<u8>, tsk: &Vec<u8>) -> Result<Self, TapError> {
        let (esk, nonce, tag, tsk) = lockbox_algorithm.encode(encapsulation_key, tsk)?;
        Ok(Self {
            name: 0,
            algorithm: lockbox_algorithm,
            esk,
            nonce,
            tag,
            tsk
        })
    }
}

#[repr(u16)]
#[derive(Debug)]
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
    pub fn encode(&self, encapsulation_key: &Vec<u8>, tsk: &Vec<u8>) -> Result<(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>), TapError> {
        use alloc::vec;
        match self {
            LockboxAlgorithm::Debug => {
                Ok((vec![], vec![], vec![], tsk.to_vec()))
            }
            LockboxAlgorithm::MlKem1024Aes256 => {
                use rand::rngs::OsRng;
                use ml_kem::{MlKem1024, KemCore, MlKem1024Params, Encoded, EncodedSizeUser, kem::{Encapsulate, EncapsulationKey}};

                let ek_bytes = Encoded::<EncapsulationKey::<MlKem1024Params>>::try_from(encapsulation_key.as_slice())?;
                let ek = <MlKem1024 as KemCore>::EncapsulationKey::from_bytes(&ek_bytes);
                let (esk, aes_key) = match ek.encapsulate(&mut OsRng) {
                    Ok(v) => v,
                    Err(_) => return Err(TapError::KemError())
                };

                use aes_gcm::{AeadInPlace, Aes256Gcm, Key, KeyInit, AeadCore};
                let mut tsk = tsk.to_vec();
                let key: &Key<Aes256Gcm> = Key::<Aes256Gcm>::from_slice(aes_key.as_slice());
                let cipher = Aes256Gcm::new(&key);
                let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
                let nonce = aes_gcm::Nonce::from_slice(&nonce);
                let tag = cipher.encrypt_in_place_detached(&nonce, b"", &mut tsk)?;

                Ok((esk.to_vec(), nonce.as_slice().to_vec(), tag.as_slice().to_vec(), tsk))
            }
        }
    }

    #[cfg(feature = "parser")]
    pub fn decode(&self, decapsulation_key: &Vec<u8>, esk: Vec<u8>, nonce: Vec<u8>, tag: Vec<u8>, mut tsk: Vec<u8>) -> Result<Vec<u8>, TapError> {
        match self {
            LockboxAlgorithm::Debug => {
                Ok(tsk)
            },
            LockboxAlgorithm::MlKem1024Aes256 => {
                use aes_gcm::{AeadInPlace, Aes256Gcm, Key, KeyInit, Tag, Nonce};
                use hybrid_array::Array;
                use ml_kem::{MlKem1024, KemCore, MlKem1024Params, Encoded, EncodedSizeUser,kem::{Decapsulate, DecapsulationKey}};

                let m = Array::try_from(esk.as_slice())?;
                let dk_bytes = Encoded::<DecapsulationKey::<MlKem1024Params>>::try_from(decapsulation_key.as_slice())?;
                let dk = <MlKem1024 as KemCore>::DecapsulationKey::from_bytes(&dk_bytes);
                let sk = match dk.decapsulate(&m) {
                    Ok(v) => v,
                    Err(_) => return Err(TapError::KemError())
                };

                let cipher = Aes256Gcm::new(Key::<Aes256Gcm>::from_slice(sk.as_slice()));
                let nonce = Nonce::from_slice(&nonce);
                let tag = Tag::from_slice(&tag);
                cipher.decrypt_in_place_detached(nonce, b"", &mut tsk, &tag).unwrap();
                Ok(tsk)
            }
        }
    }
}

pub struct Digest {
    pub pcr_id: u16,
    pub algorithm: DigestAlgorithm,
    pub value: Vec<u8>,
}

impl Digest {
    pub fn value_in_hex(&self) -> alloc::string::String {
        use crate::alloc::string::ToString;
        self.value.iter().map(|b| alloc::format!("{:02x}", b).to_string()).collect::<Vec<alloc::string::String>>().join("")
    }

    pub fn pcr_id(&self) -> u16 {
        self.pcr_id
    }
}

#[repr(u16)]
#[derive(Debug, PartialEq, Eq)]
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
            &Self::Debug => 0,
            &Self::Sha512 => 512 / 8,
        }
    }
}

pub struct Secret {
    pub name: u64,
    pub value: Vec<u8>,
}

#[repr(u16)]
#[derive(Debug)]
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