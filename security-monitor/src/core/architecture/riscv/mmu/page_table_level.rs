// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum PageTableLevel {
    Level5,
    Level4,
    Level3,
    Level2,
    Level1,
}

impl PageTableLevel {
    pub fn lower(&self) -> Option<Self> {
        match self {
            Self::Level5 => Some(Self::Level4),
            Self::Level4 => Some(Self::Level3),
            Self::Level3 => Some(Self::Level2),
            Self::Level2 => Some(Self::Level1),
            Self::Level1 => None,
        }
    }
}
