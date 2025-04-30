// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0
use crate::core::architecture::riscv::sbi::NaclSharedMemory;
use crate::core::architecture::{GeneralPurposeRegister, Hgatp, PageSize};
use crate::core::control_data::{
    ConfidentialHart, ConfidentialVm, ConfidentialVmId, ConfidentialVmMemoryLayout, ControlDataStorage, HypervisorHart, StaticMeasurements,
};
use crate::core::memory_layout::ConfidentialVmPhysicalAddress;
use crate::core::memory_protector::ConfidentialVmMemoryProtector;
use crate::core::page_allocator::{Allocated, Page, PageAllocator};
use crate::core::timer_controller::TimerController;
use crate::error::Error;
use crate::non_confidential_flow::handlers::supervisor_binary_interface::SbiResponse;
use crate::non_confidential_flow::{ApplyToHypervisorHart, NonConfidentialFlow};
use alloc::vec::Vec;
use flattened_device_tree::FlattenedDeviceTree;
use riscv_cove_tap::{AttestationPayload, AttestationPayloadParser, Secret};

const TEST_DECAPSULATION_KEY: &'static [u8] = &[
    103, 55, 81, 203, 181, 150, 84, 17, 49, 198, 99, 152, 102, 44, 180, 176, 235, 128, 121, 106, 136, 178, 129, 68, 165, 187, 200, 84, 248,
    13, 75, 53, 190, 10, 178, 65, 228, 121, 95, 143, 187, 168, 20, 245, 15, 168, 4, 152, 203, 232, 191, 104, 160, 165, 131, 164, 197, 152,
    27, 65, 223, 6, 103, 219, 97, 74, 98, 140, 48, 96, 105, 116, 56, 230, 44, 141, 54, 2, 110, 226, 156, 150, 182, 115, 191, 26, 25, 78,
    228, 148, 129, 53, 31, 77, 23, 72, 221, 1, 205, 2, 49, 66, 240, 16, 87, 20, 43, 116, 28, 186, 131, 2, 228, 50, 248, 140, 99, 208, 180,
    181, 118, 122, 195, 165, 165, 154, 250, 58, 50, 30, 101, 177, 209, 81, 24, 7, 160, 110, 22, 160, 75, 47, 16, 112, 228, 101, 88, 109,
    74, 155, 104, 226, 180, 45, 87, 163, 86, 250, 123, 179, 208, 78, 81, 177, 147, 255, 76, 117, 124, 250, 15, 21, 146, 78, 166, 228, 154,
    251, 131, 178, 145, 156, 152, 88, 105, 173, 165, 68, 51, 143, 68, 174, 150, 168, 116, 196, 37, 175, 135, 188, 115, 243, 203, 15, 210,
    98, 123, 21, 57, 177, 241, 154, 119, 227, 107, 127, 200, 23, 133, 29, 57, 189, 138, 6, 154, 108, 34, 2, 193, 116, 105, 212, 33, 165,
    136, 230, 93, 175, 69, 0, 48, 182, 103, 78, 193, 199, 52, 170, 37, 65, 75, 17, 158, 97, 178, 110, 252, 144, 223, 129, 5, 157, 43, 149,
    153, 65, 79, 147, 105, 43, 244, 90, 75, 28, 92, 192, 158, 219, 55, 177, 177, 67, 48, 38, 174, 166, 176, 32, 7, 34, 184, 25, 199, 188,
    6, 28, 83, 164, 48, 73, 146, 252, 162, 174, 226, 50, 74, 50, 74, 185, 28, 62, 93, 86, 32, 150, 184, 161, 65, 117, 105, 64, 241, 90, 40,
    0, 194, 116, 234, 79, 101, 129, 126, 99, 156, 93, 42, 39, 140, 106, 41, 79, 157, 179, 49, 248, 76, 203, 10, 16, 48, 159, 83, 10, 6,
    235, 150, 37, 115, 200, 96, 5, 193, 91, 252, 117, 49, 161, 67, 2, 99, 150, 114, 18, 151, 226, 92, 182, 85, 162, 148, 150, 75, 47, 229,
    49, 144, 95, 40, 2, 55, 107, 138, 206, 53, 174, 62, 40, 20, 186, 183, 6, 43, 193, 168, 64, 101, 125, 191, 203, 95, 65, 187, 85, 71, 86,
    151, 132, 154, 49, 226, 34, 46, 153, 85, 24, 202, 118, 64, 173, 75, 156, 238, 152, 32, 152, 65, 56, 190, 5, 16, 255, 214, 172, 34, 83,
    147, 165, 240, 203, 3, 5, 40, 205, 42, 6, 16, 231, 138, 92, 241, 176, 115, 3, 154, 109, 20, 48, 104, 197, 61, 189, 21, 161, 212, 68,
    109, 167, 179, 16, 238, 121, 93, 31, 179, 27, 47, 151, 0, 143, 131, 189, 243, 72, 165, 147, 163, 189, 203, 181, 113, 144, 123, 54, 208,
    151, 129, 98, 194, 83, 230, 245, 1, 6, 196, 99, 20, 152, 52, 171, 251, 7, 7, 216, 171, 74, 75, 171, 195, 35, 89, 138, 8, 91, 48, 151,
    100, 183, 195, 44, 157, 176, 201, 242, 213, 46, 242, 240, 11, 172, 231, 132, 104, 104, 195, 59, 130, 175, 164, 48, 164, 194, 246, 123,
    105, 138, 96, 82, 106, 22, 28, 214, 33, 21, 220, 167, 103, 194, 3, 227, 226, 204, 120, 112, 49, 167, 59, 91, 125, 186, 30, 238, 90,
    176, 75, 119, 187, 86, 155, 149, 45, 154, 21, 209, 152, 119, 152, 4, 25, 125, 35, 193, 142, 91, 5, 95, 92, 128, 135, 215, 66, 246, 68,
    24, 214, 80, 94, 112, 65, 138, 191, 198, 177, 191, 123, 179, 222, 40, 101, 153, 244, 103, 108, 248, 121, 70, 214, 81, 68, 153, 138,
    250, 225, 198, 137, 68, 158, 63, 52, 159, 208, 128, 154, 251, 133, 109, 222, 74, 148, 162, 192, 37, 141, 86, 67, 47, 64, 195, 218, 129,
    45, 63, 211, 183, 34, 89, 166, 29, 40, 130, 224, 245, 11, 53, 81, 33, 229, 100, 198, 189, 51, 54, 111, 50, 191, 74, 89, 150, 185, 153,
    137, 97, 53, 73, 37, 162, 186, 205, 244, 128, 86, 17, 132, 83, 172, 55, 146, 167, 135, 155, 113, 87, 154, 219, 101, 245, 216, 59, 30,
    214, 200, 196, 152, 54, 222, 55, 157, 170, 2, 126, 98, 185, 111, 104, 60, 22, 136, 147, 92, 179, 252, 205, 100, 50, 146, 103, 39, 62,
    96, 198, 205, 89, 186, 27, 127, 201, 17, 226, 102, 37, 39, 236, 203, 122, 71, 78, 94, 240, 12, 169, 247, 137, 163, 131, 142, 136, 146,
    66, 231, 251, 43, 8, 243, 121, 6, 19, 196, 238, 211, 201, 18, 236, 78, 176, 41, 185, 113, 9, 107, 56, 71, 39, 105, 123, 77, 220, 59,
    105, 140, 154, 109, 166, 151, 31, 164, 197, 116, 236, 209, 142, 177, 200, 76, 12, 87, 144, 21, 58, 166, 185, 219, 97, 216, 186, 192,
    166, 128, 163, 126, 214, 35, 88, 42, 126, 140, 8, 133, 235, 179, 90, 243, 65, 71, 119, 100, 54, 142, 6, 71, 177, 69, 83, 103, 35, 22,
    208, 185, 3, 23, 197, 181, 58, 167, 71, 230, 27, 71, 80, 219, 158, 99, 204, 55, 18, 144, 0, 5, 202, 36, 34, 107, 82, 62, 10, 23, 149,
    130, 200, 89, 104, 193, 7, 133, 123, 180, 21, 33, 183, 52, 43, 19, 220, 172, 70, 42, 83, 190, 56, 68, 111, 33, 66, 81, 150, 103, 180,
    139, 28, 104, 252, 175, 164, 211, 199, 227, 229, 175, 241, 99, 196, 31, 44, 27, 77, 186, 197, 69, 108, 48, 119, 96, 120, 231, 195, 167,
    19, 129, 159, 107, 154, 202, 85, 215, 125, 96, 99, 113, 131, 167, 35, 3, 87, 48, 249, 66, 133, 196, 42, 195, 88, 118, 55, 246, 106,
    195, 15, 44, 64, 57, 230, 4, 32, 150, 117, 118, 226, 123, 150, 200, 192, 4, 217, 88, 95, 51, 147, 154, 196, 79, 13, 25, 91, 53, 212,
    114, 252, 33, 144, 118, 241, 45, 9, 132, 172, 132, 71, 40, 213, 210, 38, 107, 181, 205, 139, 50, 93, 218, 73, 123, 79, 57, 123, 254,
    114, 44, 157, 118, 132, 32, 26, 146, 31, 80, 34, 113, 152, 92, 179, 243, 28, 4, 136, 76, 9, 11, 6, 54, 49, 37, 61, 196, 84, 83, 112,
    49, 242, 200, 44, 16, 161, 114, 45, 230, 197, 86, 70, 77, 201, 214, 67, 137, 218, 55, 228, 105, 72, 12, 146, 16, 101, 199, 154, 48,
    200, 60, 134, 124, 149, 43, 48, 84, 138, 107, 91, 223, 235, 110, 166, 36, 116, 128, 241, 99, 180, 39, 177, 124, 249, 72, 137, 34, 15,
    233, 52, 86, 77, 171, 144, 245, 182, 161, 22, 72, 135, 11, 101, 68, 149, 166, 105, 26, 226, 31, 234, 134, 189, 200, 196, 144, 147, 250,
    7, 233, 38, 175, 58, 186, 14, 124, 236, 33, 246, 19, 180, 153, 134, 198, 200, 161, 57, 237, 167, 11, 126, 216, 33, 26, 50, 21, 232,
    196, 62, 248, 193, 81, 174, 97, 116, 14, 248, 59, 72, 39, 96, 51, 97, 75, 88, 233, 206, 185, 146, 35, 60, 210, 29, 255, 112, 199, 166,
    247, 23, 23, 7, 162, 173, 211, 122, 203, 241, 54, 164, 235, 74, 121, 81, 127, 208, 200, 175, 240, 181, 18, 100, 53, 195, 16, 3, 49,
    242, 8, 165, 70, 201, 164, 4, 74, 143, 5, 3, 200, 173, 233, 80, 106, 1, 139, 76, 167, 198, 232, 215, 1, 32, 1, 125, 56, 177, 59, 82,
    120, 106, 133, 165, 64, 216, 27, 142, 113, 195, 118, 183, 150, 167, 33, 90, 191, 6, 80, 134, 211, 200, 14, 233, 75, 143, 9, 226, 163,
    186, 19, 184, 37, 131, 184, 37, 56, 142, 135, 186, 1, 10, 245, 7, 23, 53, 99, 120, 154, 29, 205, 8, 137, 7, 197, 43, 215, 252, 28, 105,
    48, 96, 95, 6, 15, 55, 151, 130, 17, 193, 15, 181, 113, 126, 63, 162, 145, 210, 11, 93, 67, 251, 116, 205, 71, 17, 57, 75, 0, 39, 228,
    28, 82, 181, 35, 121, 116, 112, 83, 44, 190, 18, 60, 146, 149, 7, 32, 229, 226, 85, 37, 101, 119, 212, 225, 86, 235, 212, 198, 152,
    216, 19, 64, 92, 97, 67, 11, 151, 134, 148, 172, 222, 120, 3, 30, 116, 186, 29, 133, 23, 218, 226, 52, 111, 0, 132, 17, 35, 31, 204,
    231, 191, 247, 91, 195, 97, 230, 145, 231, 118, 4, 144, 4, 9, 123, 54, 73, 13, 135, 98, 136, 112, 27, 45, 58, 23, 67, 171, 135, 83,
    212, 122, 198, 32, 14, 45, 167, 69, 141, 58, 5, 150, 129, 35, 56, 114, 121, 78, 103, 32, 24, 107, 32, 16, 139, 29, 16, 51, 151, 28,
    225, 158, 214, 122, 42, 40, 228, 153, 163, 96, 164, 173, 134, 174, 65, 148, 3, 79, 32, 47, 143, 163, 98, 111, 231, 95, 48, 122, 76,
    234, 65, 72, 33, 155, 149, 142, 160, 183, 136, 102, 89, 35, 90, 77, 25, 128, 177, 146, 97, 8, 71, 216, 110, 243, 39, 57, 249, 76, 59,
    68, 108, 77, 129, 216, 155, 139, 66, 42, 157, 7, 156, 136, 177, 26, 202, 243, 33, 176, 20, 41, 78, 24, 178, 150, 229, 47, 63, 116, 76,
    249, 99, 74, 79, 176, 29, 176, 217, 158, 242, 10, 99, 58, 85, 46, 118, 160, 88, 92, 97, 9, 240, 24, 118, 139, 118, 58, 243, 103, 139,
    71, 128, 8, 156, 19, 66, 185, 105, 7, 162, 154, 28, 17, 82, 28, 116, 76, 39, 151, 208, 191, 43, 156, 205, 202, 97, 70, 114, 180, 80,
    118, 119, 63, 69, 138, 49, 239, 134, 155, 225, 235, 46, 254, 181, 13, 14, 55, 73, 93, 197, 202, 85, 224, 117, 40, 147, 79, 98, 147,
    196, 22, 128, 39, 208, 229, 61, 7, 250, 204, 102, 48, 203, 8, 25, 126, 83, 251, 25, 58, 23, 17, 53, 220, 138, 217, 151, 148, 2, 167,
    27, 105, 38, 188, 220, 220, 71, 185, 52, 1, 145, 10, 95, 204, 26, 129, 59, 104, 43, 9, 186, 122, 114, 210, 72, 109, 108, 121, 149, 22,
    70, 92, 20, 114, 155, 38, 148, 155, 11, 124, 188, 124, 100, 15, 38, 127, 237, 128, 177, 98, 197, 31, 216, 224, 146, 39, 193, 1, 213, 5,
    168, 250, 232, 162, 215, 5, 78, 40, 167, 139, 168, 117, 13, 236, 249, 5, 124, 131, 151, 159, 122, 187, 8, 73, 69, 100, 128, 6, 197,
    178, 136, 4, 243, 78, 115, 178, 56, 17, 26, 101, 161, 245, 0, 177, 204, 96, 106, 132, 143, 40, 89, 7, 11, 235, 167, 87, 49, 121, 243,
    97, 73, 207, 88, 1, 191, 137, 161, 195, 140, 194, 120, 65, 85, 40, 208, 59, 219, 148, 63, 150, 40, 12, 140, 197, 32, 66, 217, 185, 31,
    170, 157, 110, 167, 188, 187, 122, 177, 137, 122, 50, 102, 150, 111, 120, 57, 52, 38, 199, 109, 138, 73, 87, 139, 152, 177, 89, 235,
    180, 110, 224, 168, 131, 162, 112, 216, 5, 124, 208, 35, 28, 134, 144, 106, 145, 219, 186, 222, 107, 36, 105, 88, 30, 43, 202, 47, 234,
    131, 137, 247, 199, 75, 205, 112, 150, 30, 165, 185, 52, 251, 207, 154, 101, 144, 191, 134, 184, 219, 84, 136, 84, 217, 163, 251, 48,
    17, 4, 51, 189, 122, 27, 101, 156, 168, 86, 128, 133, 99, 146, 55, 179, 189, 195, 123, 127, 167, 22, 212, 130, 162, 91, 84, 16, 107,
    58, 143, 84, 211, 170, 153, 181, 18, 61, 169, 96, 102, 144, 69, 146, 243, 165, 78, 226, 58, 121, 129, 171, 96, 138, 47, 68, 19, 204,
    101, 137, 70, 198, 215, 120, 14, 167, 101, 100, 75, 60, 192, 108, 112, 3, 74, 180, 235, 53, 25, 18, 231, 113, 91, 86, 117, 93, 9, 2,
    21, 113, 191, 52, 10, 185, 37, 152, 162, 78, 129, 24, 147, 25, 91, 150, 161, 98, 159, 128, 65, 245, 134, 88, 67, 21, 97, 252, 10, 177,
    82, 146, 185, 19, 236, 71, 63, 4, 71, 155, 193, 69, 205, 76, 86, 58, 40, 98, 53, 100, 108, 211, 5, 169, 190, 16, 20, 226, 199, 177, 48,
    195, 62, 183, 124, 196, 160, 217, 120, 107, 214, 188, 42, 149, 75, 243, 0, 87, 120, 248, 145, 124, 225, 55, 137, 187, 185, 98, 128,
    120, 88, 182, 119, 49, 87, 43, 109, 60, 155, 75, 82, 6, 250, 201, 167, 200, 150, 22, 152, 216, 131, 36, 169, 21, 24, 104, 153, 178,
    153, 35, 240, 132, 66, 163, 211, 134, 189, 65, 107, 204, 154, 16, 1, 100, 201, 48, 236, 53, 234, 251, 106, 179, 88, 81, 182, 200, 206,
    99, 119, 54, 106, 23, 95, 61, 117, 41, 140, 81, 141, 68, 137, 137, 51, 245, 61, 238, 97, 113, 69, 9, 51, 121, 196, 101, 159, 104, 88,
    59, 43, 40, 18, 38, 102, 190, 197, 120, 56, 153, 31, 241, 108, 54, 141, 210, 44, 54, 231, 128, 201, 26, 53, 130, 226, 94, 25, 121, 76,
    107, 242, 171, 66, 69, 138, 141, 215, 112, 93, 226, 194, 170, 32, 192, 84, 232, 75, 62, 243, 80, 50, 121, 134, 38, 194, 72, 38, 50, 83,
    167, 26, 17, 148, 53, 113, 52, 10, 151, 140, 208, 166, 2, 228, 125, 238, 84, 10, 136, 20, 186, 6, 243, 20, 20, 121, 124, 223, 96, 73,
    88, 35, 97, 187, 171, 163, 135, 168, 61, 137, 145, 63, 228, 192, 193, 18, 185, 86, 33, 164, 189, 168, 18, 58, 20, 209, 168, 66, 251,
    87, 184, 58, 79, 186, 243, 58, 142, 85, 34, 56, 165, 150, 170, 231, 161, 80, 215, 93, 166, 72, 188, 68, 100, 73, 119, 186, 31, 135,
    164, 198, 138, 140, 75, 210, 69, 183, 208, 7, 33, 247, 214, 78, 130, 43, 8, 91, 144, 19, 18, 236, 55, 168, 22, 152, 2, 22, 12, 206, 17,
    96, 240, 16, 190, 140, 188, 172, 232, 231, 176, 5, 215, 131, 146, 52, 167, 7, 134, 131, 9, 208, 55, 132, 180, 39, 59, 28, 138, 22, 1,
    51, 237, 41, 129, 132, 112, 70, 37, 242, 156, 250, 8, 109, 19, 38, 62, 229, 137, 145, 35, 197, 150, 186, 120, 142, 92, 84, 168, 233,
    186, 130, 155, 138, 157, 144, 75, 196, 188, 11, 190, 167, 107, 197, 63, 248, 17, 33, 69, 152, 71, 44, 156, 32, 43, 115, 239, 240, 53,
    220, 9, 112, 58, 247, 191, 27, 171, 170, 199, 49, 147, 203, 70, 17, 122, 124, 148, 146, 164, 63, 201, 87, 137, 169, 36, 197, 145, 39,
    135, 178, 226, 9, 14, 187, 207, 211, 121, 98, 33, 240, 109, 235, 249, 207, 112, 224, 86, 184, 185, 22, 29, 99, 71, 244, 115, 53, 243,
    225, 119, 109, 164, 187, 135, 193, 92, 200, 38, 20, 111, 240, 36, 154, 65, 59, 69, 170, 147, 168, 5, 25, 110, 164, 83, 17, 75, 82, 78,
    49, 10, 237, 170, 70, 227, 185, 150, 66, 54, 135, 130, 86, 109, 4, 154, 114, 109, 108, 202, 145, 9, 147, 174, 214, 33, 208, 20, 158,
    165, 136, 169, 171, 217, 9, 219, 182, 154, 162, 40, 41, 217, 184, 58, 218, 34, 9, 166, 194, 101, 159, 33, 105, 214, 104, 185, 49, 72,
    66, 198, 226, 42, 116, 149, 139, 76, 37, 187, 220, 210, 147, 217, 156, 182, 9, 216, 102, 116, 154, 72, 93, 251, 86, 2, 72, 131, 207,
    84, 101, 219, 160, 54, 50, 6, 88, 127, 69, 89, 127, 137, 0, 47, 184, 96, 114, 50, 19, 142, 3, 178, 168, 148, 82, 95, 38, 83, 112, 5,
    75, 72, 134, 54, 20, 71, 43, 149, 208, 162, 48, 52, 66, 227, 120, 176, 221, 28, 117, 172, 186, 185, 113, 169, 168, 209, 40, 28, 121,
    97, 58, 206, 198, 147, 60, 55, 123, 60, 87, 140, 42, 97, 161, 236, 24, 27, 16, 18, 151, 163, 124, 197, 25, 123, 41, 66, 246, 160, 228,
    112, 76, 14, 198, 53, 64, 72, 27, 159, 21, 157, 194, 85, 181, 155, 181, 93, 244, 150, 174, 84, 33, 123, 118, 137, 189, 81, 219, 160,
    56, 58, 61, 114, 216, 82, 255, 202, 118, 223, 5, 182, 110, 236, 203, 212, 123, 197, 48, 64, 129, 118, 40, 199, 30, 54, 29, 106, 248,
    137, 8, 73, 22, 180, 8, 164, 102, 201, 110, 112, 134, 196, 166, 10, 16, 252, 247, 83, 123, 185, 74, 251, 204, 125, 67, 117, 144, 145,
    156, 40, 101, 12, 79, 35, 104, 37, 146, 38, 169, 191, 218, 58, 58, 11, 161, 181, 8, 125, 157, 118, 68, 47, 215, 134, 198, 248, 28, 104,
    192, 54, 13, 113, 148, 215, 7, 44, 69, 51, 174, 168, 108, 45, 31, 140, 10, 39, 105, 96, 102, 246, 207, 209, 16, 3, 247, 151, 39, 11,
    50, 56, 151, 19, 207, 250, 9, 61, 153, 27, 99, 132, 76, 56, 94, 114, 39, 127, 22, 111, 90, 57, 52, 214, 187, 137, 164, 120, 141, 226,
    131, 33, 222, 252, 116, 87, 171, 72, 75, 211, 9, 134, 220, 29, 171, 48, 8, 205, 123, 34, 246, 151, 2, 250, 187, 154, 16, 69, 64, 125,
    164, 121, 28, 53, 144, 255, 89, 157, 129, 214, 136, 207, 167, 204, 18, 166, 140, 80, 245, 26, 16, 9, 65, 27, 68, 133, 15, 144, 21, 220,
    132, 169, 59, 23, 199, 162, 7, 85, 44, 102, 30, 169, 131, 142, 49, 185, 94, 173, 84, 98, 72, 229, 107, 231, 165, 19, 5, 5, 38, 135,
    113, 25, 152, 128, 161, 65, 119, 26, 158, 71, 172, 254, 213, 144, 203, 58, 167, 203, 124, 95, 116, 145, 29, 137, 18, 194, 157, 98, 51,
    244, 213, 59, 198, 65, 57, 226, 245, 91, 231, 85, 7, 221, 119, 134, 142, 56, 74, 236, 88, 31, 63, 65, 29, 177, 167, 66, 151, 45, 62,
    191, 211, 49, 92, 132, 165, 173, 99, 160, 231, 92, 139, 202, 62, 48, 65, 224, 93, 144, 103, 175, 243, 177, 36, 79, 118, 62, 121, 131,
    212, 139, 163, 65, 52, 186, 184, 141, 99, 93, 140, 248, 255, 93, 104, 96, 88, 250, 104, 182, 194, 254, 234, 165, 250, 77, 230, 87, 87,
    8, 108, 1, 37, 233, 55, 188, 192, 208, 47, 170, 137, 136, 174, 113, 105, 223, 7, 246, 167, 113, 230, 231, 254, 58, 182, 94, 150, 92,
    99, 195, 228, 14, 217, 9,
];

/// Creates a confidential VM in a single-step. This handler implements the Promote to TVM call defined by the COVH ABI in the CoVE
/// specification. With this call, the hypervisor presents a state of a virtual machine, requesting the security monitor to promote it to a
/// confidential VM. The security monitor copies the VM state (data, page tables, boot hart state) into the confidential memory and measures
/// it.
///
/// # Safety
///
/// * The virtual machine initial state must consist of only one hart (boot hart) running. All other hart must be still in reset state.
/// * The address of the flattened device tree must be aligned to 8 bytes.
/// * The address of the authentication blob must be either `0` or aligned to 8 bytes.
pub struct PromoteToConfidentialVm {
    fdt_address: ConfidentialVmPhysicalAddress,
    attestation_payload_address: Option<ConfidentialVmPhysicalAddress>,
    program_counter: usize,
    hgatp: Hgatp,
}

impl PromoteToConfidentialVm {
    const FDT_ALIGNMENT_IN_BYTES: usize = 8;
    const TAP_ALIGNMENT_IN_BYTES: usize = 4;
    const BOOT_HART_ID: usize = 0;

    pub fn from_hypervisor_hart(hypervisor_hart: &HypervisorHart) -> Self {
        let fdt_address = ConfidentialVmPhysicalAddress::new(hypervisor_hart.gprs().read(GeneralPurposeRegister::a0));
        let attestation_payload_address = match hypervisor_hart.gprs().read(GeneralPurposeRegister::a1) {
            0 => None,
            address => Some(ConfidentialVmPhysicalAddress::new(address)),
        };
        let program_counter = hypervisor_hart.gprs().read(GeneralPurposeRegister::a2);
        let hgatp = Hgatp::from(hypervisor_hart.csrs().hgatp.read());
        Self { fdt_address, attestation_payload_address, program_counter, hgatp }
    }

    pub fn handle(self, mut non_confidential_flow: NonConfidentialFlow) -> ! {
        let htimedelta = 0_i64.wrapping_sub(TimerController::read_time() as i64) as usize;
        debug!("htimedelta={:x}", htimedelta);

        crate::core::architecture::CSR.mstatus.read_and_set_bits(crate::core::architecture::specification::SR_FS);
        unsafe { non_confidential_flow.hypervisor_hart_mut().hypervisor_hart_state_mut().fprs_mut().save_in_main_memory() };
        let sbi_response = match self.create_confidential_vm(non_confidential_flow.shared_memory(), htimedelta) {
            Ok(confidential_vm_id) => {
                debug!("Created new confidential VM[id={:?}]", confidential_vm_id);
                SbiResponse::success_with_code(confidential_vm_id.usize())
            }
            Err(error) => {
                debug!("Promotion to confidential VM failed: {:?}", error);
                SbiResponse::error(error)
            }
        };
        unsafe { non_confidential_flow.hypervisor_hart_mut().hypervisor_hart_state_mut().fprs_mut().restore_from_main_memory() };

        non_confidential_flow.apply_and_exit_to_hypervisor(ApplyToHypervisorHart::PromoteResponse((self, sbi_response, htimedelta)))
    }

    pub fn apply_to_hypervisor_hart(&self, hypervisor_hart: &mut HypervisorHart, sbi_response: SbiResponse, htimedelta: usize) {
        use crate::core::architecture::specification::CSR_HTIMEDELTA;
        hypervisor_hart.shared_memory_mut().write_csr(CSR_HTIMEDELTA.into(), htimedelta);
        sbi_response.apply_to_hypervisor_hart(hypervisor_hart);
    }

    fn create_confidential_vm(&self, shared_memory: &NaclSharedMemory, htimedelta: usize) -> Result<ConfidentialVmId, Error> {
        debug!("Promoting a VM to a confidential VM");
        // Copying the entire VM's state to the confidential memory, recreating the MMU configuration
        let mut memory_protector = ConfidentialVmMemoryProtector::from_vm_state(&self.hgatp)?;

        // The pointer to the flattened device tree (FDT) as well as the entire FDT must be treated as an untrusted input, which measurement
        // is reflected during attestation. We can parse FDT only after moving VM's data (and the FDT) to the confidential memory.
        let (vm_memory_layout, number_of_confidential_harts) = self.process_device_tree(&memory_protector)?;

        // We create a fixed number of harts (all but the boot hart are in the reset state).
        let confidential_harts: Vec<_> = (0..number_of_confidential_harts)
            .map(|confidential_hart_id| match confidential_hart_id {
                Self::BOOT_HART_ID => {
                    ConfidentialHart::from_vm_hart(confidential_hart_id, self.program_counter, self.fdt_address, htimedelta, shared_memory)
                }
                _ => ConfidentialHart::from_vm_hart_reset(confidential_hart_id, htimedelta, shared_memory),
            })
            .collect();

        let attestation_payload =
            self.read_attestation_payload(&memory_protector).inspect_err(|e| debug!("TAP reading failed: {:?}", e)).unwrap_or(None);
        let measurements = self.measure(&mut memory_protector, &vm_memory_layout, &confidential_harts)?;

        let secrets = self
            .authenticate_and_authorize_vm(attestation_payload, &measurements)
            .inspect_err(|e| debug!("Local attestation failed: {:?}", e))
            .unwrap_or(alloc::vec![]);

        ControlDataStorage::try_write(|control_data| {
            // We have a write lock on the entire control data! Spend here as little time as possible because we are
            // blocking all other harts from accessing the control data. This influences all confidential VMs in the system!
            let id = control_data.unique_id()?;
            control_data.insert_confidential_vm(ConfidentialVm::new(id, confidential_harts, measurements, secrets, memory_protector))
        })
    }

    fn measure(
        &self, memory_protector: &mut ConfidentialVmMemoryProtector, vm_memory_layout: &ConfidentialVmMemoryLayout,
        confidential_harts: &Vec<ConfidentialHart>,
    ) -> Result<StaticMeasurements, Error> {
        let mut measurements = StaticMeasurements::default();
        memory_protector.finalize(&mut measurements, vm_memory_layout)?;
        confidential_harts[Self::BOOT_HART_ID].measure(measurements.pcr_boot_hart_mut());
        debug!("VM measurements: {:?}", measurements);
        Ok(measurements)
    }

    fn process_device_tree(&self, memory_protector: &ConfidentialVmMemoryProtector) -> Result<(ConfidentialVmMemoryLayout, usize), Error> {
        debug!("Reading flatten device tree (FDT) at memory address {:?}", self.fdt_address);
        let address_in_confidential_memory = memory_protector.translate_address(&self.fdt_address)?;
        // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be within
        // the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 4 bytes).
        ensure!(address_in_confidential_memory.is_aligned_to(Self::FDT_ALIGNMENT_IN_BYTES), Error::FdtNotAlignedTo64Bits())?;
        // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the not-yet-created
        // confidential VM's and (2) there is only one physical hart executing this code.
        let fdt_total_size = unsafe { FlattenedDeviceTree::total_size(address_in_confidential_memory.to_ptr())? };
        ensure!(fdt_total_size >= FlattenedDeviceTree::FDT_HEADER_SIZE, Error::FdtInvalidSize())?;

        // To work with FDT, we must have it as a continous chunk of memory. We accept only FDTs that fit within 2 MiB
        ensure!(fdt_total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::FdtInvalidSize())?;
        let large_page = Self::relocate(memory_protector, &self.fdt_address, fdt_total_size, false)?;

        // Security note: We parse untrusted FDT using an external library. A vulnerability in this library might blow up our security
        // guarantees! Below unsafe is ok because the FDT address aligned to (at least) the size of the FDT header and all FDT is in a
        // continuous chunk of memory. See the safety requirements of `FlattenedDeviceTree::from_raw_pointer`.
        let device_tree = unsafe { FlattenedDeviceTree::from_raw_pointer(large_page.address().to_ptr()) }?;

        let number_of_confidential_harts = device_tree.harts().count();
        let kernel = device_tree.memory().and_then(|r| r.into_range())?;
        let initrd = device_tree.initrd().ok();

        let vm_memory_layout =
            ConfidentialVmMemoryLayout::new(kernel, (self.fdt_address.usize(), self.fdt_address.usize() + fdt_total_size), initrd);
        debug!("Virtual machine's memory layout: {:?}", vm_memory_layout);

        // Clean up, deallocate pages
        PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);

        ensure!(number_of_confidential_harts > 0, Error::InvalidNumberOfHartsInFdt())?;
        ensure!(number_of_confidential_harts < ConfidentialVm::MAX_NUMBER_OF_HARTS_PER_VM, Error::InvalidNumberOfHartsInFdt())?;

        Ok((vm_memory_layout, number_of_confidential_harts))
    }

    fn read_attestation_payload(&self, memory_protector: &ConfidentialVmMemoryProtector) -> Result<Option<AttestationPayload>, Error> {
        match self.attestation_payload_address {
            Some(attestation_payload_address) => {
                debug!("Reading TEE attestation payload (TAP) at memory address {:?}", attestation_payload_address);
                let address_in_confidential_memory = memory_protector.translate_address(&attestation_payload_address)?;
                // Make sure that the address is 8-bytes aligned. Once we ensure this, we can safely read 8 bytes because they must be
                // within the page boundary. These 8 bytes should contain the `magic` (first 4 bytes) and `size` (next 2
                // bytes).
                ensure!(address_in_confidential_memory.is_aligned_to(Self::TAP_ALIGNMENT_IN_BYTES), Error::AuthBlobNotAlignedTo32Bits())?;
                // Below use of unsafe is ok because (1) the security monitor owns the memory region containing the data of the
                // not-yet-created confidential VM's and (2) there is only one physical hart executing this code.
                let header: u64 =
                    unsafe { address_in_confidential_memory.read_volatile().try_into().map_err(|_| Error::AuthBlobNotAlignedTo32Bits())? };
                let total_size = riscv_cove_tap::ACE_HEADER_SIZE + ((header >> 32) & 0xFFFF) as usize;
                // To work with the authentication blob, we must have it as a continous chunk of memory. We accept only authentication blobs
                // that fit within 2MiB
                ensure!(total_size.div_ceil(PageSize::Size2MiB.in_bytes()) == 1, Error::AuthBlobInvalidSize())?;
                let large_page = Self::relocate(memory_protector, &attestation_payload_address, total_size, true)?;
                // TODO: replace the hardcoded decapsulation key with a key or interface to device-specific decapsulation key
                let mut parser = unsafe { AttestationPayloadParser::from_raw_pointer(large_page.address().to_ptr(), total_size)? };
                let attestation_payload = parser.parse_and_verify(TEST_DECAPSULATION_KEY)?;
                // Clean up, deallocate pages
                PageAllocator::release_pages(alloc::vec![large_page.deallocate()]);
                Ok(Some(attestation_payload))
            }
            None => Ok(None),
        }
    }

    /// Performs local attestation. It decides if the VM can be promote into a confidential VM and decrypts the attestation secret intended
    /// for this confidential VM.
    fn authenticate_and_authorize_vm(
        &self, attestation_payload: Option<AttestationPayload>, measurements: &StaticMeasurements,
    ) -> Result<Vec<Secret>, Error> {
        use crate::core::control_data::MeasurementDigest;
        match attestation_payload {
            Some(attestation_payload) => {
                ensure!(attestation_payload.digests.len() > 0, Error::LocalAttestationFailed())?;
                for digest in attestation_payload.digests.iter() {
                    debug!("Reference PCR{:?}={:?}=0x{}", digest.pcr_id, digest.algorithm, digest.value_in_hex());
                    ensure!(digest.algorithm == riscv_cove_tap::DigestAlgorithm::Sha512, Error::LocalAttestationNotSupportedDigest())?;
                    let pcr_value = MeasurementDigest::clone_from_slice(&digest.value);
                    ensure!(measurements.compare(digest.pcr_id() as usize, pcr_value)?, Error::LocalAttestationFailed())?;
                }
                debug!("Attestation succeeded, fetched {} secrets", attestation_payload.secrets.len());
                Ok(attestation_payload.secrets)
            }
            None => Ok(alloc::vec![]),
        }
    }

    /// Copies a buffer into a single large page.
    ///
    /// Why do we need this function? The input buffer is continuous across guest physical pages with G-stage address
    /// translation enabled but might not be continuous across the real physical pages. The output buffer is continous accross real
    /// physical pages. Returns error if (1) the buffer to copy is larger than 2 MiB page, or (2) the base address is not aligned to
    /// 8-bytes.
    ///
    /// Safety:
    ///   * The caller of this function is responsible for deallocating the page returned from this function.
    fn relocate(
        memory_protector: &ConfidentialVmMemoryProtector, base_address: &ConfidentialVmPhysicalAddress, number_of_bytes_to_copy: usize,
        clear: bool,
    ) -> Result<Page<Allocated>, Error> {
        ensure!((base_address.usize() as *const u8).is_aligned_to(core::mem::size_of::<usize>()), Error::AddressNotAligned())?;
        let mut large_page = PageAllocator::acquire_page(PageSize::Size2MiB)?.zeroize();
        // Let's copy a blob from confidential VM's pages into the newly allocated huge page. We will copy in chunks of 8-bytes (usize).
        let mut copied_bytes = 0;
        while copied_bytes < number_of_bytes_to_copy {
            let confidential_vm_physical_address = base_address.add(copied_bytes);
            let confidential_memory_address = memory_protector.translate_address(&confidential_vm_physical_address)?;
            let value: usize = unsafe { confidential_memory_address.read_volatile() };
            if clear {
                unsafe { confidential_memory_address.write_volatile(0) };
            }
            large_page.write(copied_bytes, value)?;
            copied_bytes += core::mem::size_of::<usize>();
        }
        Ok(large_page)
    }
}
