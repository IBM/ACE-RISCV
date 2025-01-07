// SPDX-FileCopyrightText: 2023 IBM Corporation
// SPDX-FileContributor: Wojciech Ozga <woz@zurich.ibm.com>, IBM Research - Zurich
// SPDX-License-Identifier: Apache-2.0

// Safety:
//   - Maintain lexicographic ordering based on the top-to-bottom declaration to ensure that PartialOrd derivative works correctly.
#[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
#[rr::refined_by("page_table_level")]
pub enum PageTableLevel {
    #[rr::pattern("PTLevel1")]
    Level1,
    #[rr::pattern("PTLevel2")]
    Level2,
    #[rr::pattern("PTLevel3")]
    Level3,
    #[rr::pattern("PTLevel4")]
    Level4,
    #[rr::pattern("PTLevel5")]
    Level5,
}

impl PageTableLevel {
    #[rr::trust_me]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("<#>@{option} (page_table_level_lower x)")]
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
