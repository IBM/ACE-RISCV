// SPDX-FileCopyrightText: 2024 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::confidential_flow::handlers::sbi::SbiResponse;
use crate::confidential_flow::{ApplyToConfidentialHart, ConfidentialFlow};
use crate::core::architecture::{GeneralPurposeRegister, PageSize};
use crate::core::control_data::{ConfidentialHart, ControlDataStorage};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::error::Error;

/// Provides the confidential VM with a secret that was decoded from the attestation payload during the promotion of the VM to confidential
/// VM. Secret is written to the buffer allocated by the confidential VM and passed as arguments to the call.
pub struct RetrieveSecretRequest {
    output_buffer_address: usize,
    output_buffer_size: usize,
}

impl RetrieveSecretRequest {
    pub const ADDRESS_ALIGNMENT: usize = core::mem::size_of::<usize>();

    pub fn from_confidential_hart(confidential_hart: &ConfidentialHart) -> Self {
        Self {
            output_buffer_address: confidential_hart.gprs().read(GeneralPurposeRegister::a0),
            output_buffer_size: confidential_hart.gprs().read(GeneralPurposeRegister::a1),
        }
    }

    pub fn handle(self, confidential_flow: ConfidentialFlow) -> ! {
        let transformation = ControlDataStorage::try_confidential_vm(confidential_flow.confidential_vm_id(), |ref confidential_vm| {
            let output_buffer_address = ConfidentialVmPhysicalAddress::new(self.output_buffer_address)?;
            ensure!(output_buffer_address.is_aligned_to(Self::ADDRESS_ALIGNMENT), Error::AddressNotAligned())?;
            ensure!(self.output_buffer_size <= PageSize::Size4KiB.in_bytes(), Error::AddressNotAligned())?;
            let secret = confidential_vm.secret(0)?;
            ensure!(secret.len() <= self.output_buffer_size, Error::AddressNotAligned())?;
            const WORD_SIZE: usize = core::mem::size_of::<usize>();
            for chunk in 0..secret.len().div_ceil(WORD_SIZE) {
                let byte_offset = chunk * WORD_SIZE;
                let chunk_len = core::cmp::min(WORD_SIZE, secret.len() - byte_offset);
                let mut buffer = [0u8; WORD_SIZE];
                buffer[..chunk_len].copy_from_slice(&secret[byte_offset..byte_offset + chunk_len]);
                let confidential_memory_address =
                    confidential_vm.memory_protector().translate_address(&output_buffer_address.add(byte_offset))?;
                unsafe { confidential_memory_address.write_volatile(usize::from_le_bytes(buffer)) };
            }
            Ok(SbiResponse::success_with_code(secret.len()))
        })
        .unwrap_or_else(|error| SbiResponse::error(error));
        confidential_flow.apply_and_exit_to_confidential_hart(ApplyToConfidentialHart::SbiResponse(transformation))
    }
}
