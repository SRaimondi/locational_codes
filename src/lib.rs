/// Small helper trait to implement for a type to be able to represent child for
/// a locational code.
pub trait Child {
    fn to_bits(self) -> u64;
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LocationalCodeError {
    InvalidCodeWithSentinel,
    InvalidCodeWithoutSentinel,
    InvalidDepth,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct LocationalCode<const PLB: u32> {
    bits: u64,
}

impl<const PLB: u32> LocationalCode<PLB> {
    /// Number of bits used to represent each level of the code (2 for 2D, 3 for 3D).
    const PER_LEVEL_BITS: u32 = PLB;
    /// Maximum inclusive depth the code can represent for the bits we use at each level.
    pub const MAX_INCLUSIVE_DEPTH: u32 = (u64::BITS - 1) / Self::PER_LEVEL_BITS - 1;
    /// Smallest valid code.
    const SMALLEST_CODE: u64 = 1 << Self::PER_LEVEL_BITS;
    /// Largest valid code.
    const LARGEST_CODE: u64 =
        (1 << ((Self::MAX_INCLUSIVE_DEPTH + 1) * Self::PER_LEVEL_BITS + 1)) - 1;
    /// Largest valid code with no sentinel
    const LARGEST_CODE_NO_SENTINEL: u64 = Self::unset_msb(Self::LARGEST_CODE);

    /// Helper function to find the index of the most significant bit.
    #[inline]
    pub const fn msb_index(v: u64) -> u32 {
        u64::BITS - 1 - v.leading_zeros()
    }

    /// Set the most significant bit to 0.
    #[inline]
    pub const fn unset_msb(v: u64) -> u64 {
        v ^ (1 << Self::msb_index(v))
    }

    /// Helper function to check if a code is in the valid range.
    fn is_valid_code(code: u64) -> bool {
        (Self::SMALLEST_CODE..=Self::LARGEST_CODE).contains(&code)
    }

    /// Helper function to check that a code without the sentinel is in the valid range.
    fn is_valid_code_without_sentinel(code: u64) -> bool {
        (0..=Self::LARGEST_CODE_NO_SENTINEL).contains(&code)
    }

    /// Helper function to check if a depth is valid.
    fn is_valid_depth(depth: u32) -> bool {
        depth <= Self::MAX_INCLUSIVE_DEPTH
    }

    /// Helper function that adds the sentinel bit to a given raw code for the given depth.
    /// Panics in debug mode if the code or the depth are invalid.
    #[inline]
    fn add_sentinel_bit(code: u64, depth: u32) -> u64 {
        debug_assert!(Self::is_valid_code_without_sentinel(code));
        debug_assert!(Self::is_valid_depth(depth));
        let sentinel_index = (depth + 1) * Self::PER_LEVEL_BITS;
        let sentinel_mask = 1 << sentinel_index;
        debug_assert!(code < sentinel_mask);
        code | sentinel_mask
    }

    /// Computes the maximum index along a single axis. Equals to 2^(depth + 1).
    /// Panics if the given depth is larger than the maximum allowed.
    #[inline]
    fn max_index_for_depth(depth: u32) -> u32 {
        assert!(Self::is_valid_depth(depth));
        1 << (depth + 1)
    }

    pub fn new_root(child: impl Child) -> Self {
        Self {
            bits: (1 << Self::PER_LEVEL_BITS) | child.to_bits(),
        }
    }

    /// Create a new locational code from the given raw code.
    /// # Safety
    /// The code is expected to be valid as there is no check on it for this constructor.
    pub unsafe fn new_from_code_unchecked(code: u64) -> Self {
        debug_assert!(Self::is_valid_code(code));
        Self { bits: code }
    }

    /// Create a new locational code from the given code, check that the given value is within the
    /// valid range.
    pub fn new_from_code(code: u64) -> Result<Self, LocationalCodeError> {
        if Self::is_valid_code(code) {
            Ok(unsafe { Self::new_from_code_unchecked(code) })
        } else {
            Err(LocationalCodeError::InvalidCodeWithSentinel)
        }
    }

    /// Create a new locational code for the given code and depth.
    /// # Safety
    /// The code is expected to be valid and the depth too, no check is done on neither of them.
    pub unsafe fn new_from_code_and_depth_unchecked(code: u64, depth: u32) -> Self {
        Self::new_from_code_unchecked(Self::add_sentinel_bit(code, depth))
    }

    /// Create a new locational code from the given code and depth. Checks both the code
    /// and the depth to be valid.
    pub fn new_from_code_and_depth(code: u64, depth: u32) -> Result<Self, LocationalCodeError> {
        if !Self::is_valid_code_without_sentinel(code) {
            Err(LocationalCodeError::InvalidCodeWithoutSentinel)
        } else if !Self::is_valid_depth(depth) {
            Err(LocationalCodeError::InvalidDepth)
        } else {
            Ok(unsafe { Self::new_from_code_and_depth_unchecked(code, depth) })
        }
    }

    /// Computes the depth of the code starting from 0.
    #[inline]
    pub fn depth(self) -> u32 {
        Self::msb_index(self.bits) / Self::PER_LEVEL_BITS - 1
    }

    /// Checks if a code can have children codes.
    #[inline]
    pub fn can_have_children(self) -> bool {
        self.depth() < Self::MAX_INCLUSIVE_DEPTH
    }

    /// Computes the locational code of the parent. We call the unsafe constructor here as we trust
    /// that the code used in the call is a valid one.
    #[inline]
    pub fn parent_code(self) -> Option<Self> {
        if Self::msb_index(self.bits) == Self::PER_LEVEL_BITS {
            None
        } else {
            // The parent code is simply computed by removing the bits of the current level
            Some(unsafe { Self::new_from_code_unchecked(self.bits >> Self::PER_LEVEL_BITS) })
        }
    }

    /// Compute the locational code of the child without checking if self can have children.
    /// # Safety
    /// The caller must be sure it's possible to compute a child code without loss of bits.
    #[inline]
    pub unsafe fn child_code_unchecked(self, child: impl Child) -> Self {
        Self::new_from_code_unchecked((self.bits << Self::PER_LEVEL_BITS) | child.to_bits())
    }

    /// Compute the LC of the child code for a type that can be converted to u64.
    #[inline]
    pub fn child_code(self, child: impl Child) -> Option<Self> {
        if self.can_have_children() {
            Some(unsafe { self.child_code_unchecked(child) })
        } else {
            None
        }
    }
}

macro_rules! locational_code_debug {
    ($t:ty, $s:expr) => {
        impl std::fmt::Debug for $t {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, $s, self.bits)
            }
        }
    };
}

locational_code_debug!(LocationalCode2D, "LocationalCode2D: 0b{:b}");
locational_code_debug!(LocationalCode3D, "LocationalCode3D: 0b{:b}");

/// Alias type for 2D locational code.
pub type LocationalCode2D = LocationalCode<2>;
/// Alias type for 3D locational code.
pub type LocationalCode3D = LocationalCode<3>;

/// Helper enum representing the possible children for a 2D locational code.
/// The value is set such that the bits are already the morton codes for a 2x2 grid.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum Child2D {
    BottomLeft = 0b00,
    BottomRight = 0b01,
    TopLeft = 0b10,
    TopRight = 0b11,
}

impl Child2D {
    /// Return an iterator over all possible values.
    #[inline]
    pub fn iter() -> std::slice::Iter<'static, Self> {
        const CHILDREN: [Child2D; 4] = [
            Child2D::BottomLeft,
            Child2D::BottomRight,
            Child2D::TopLeft,
            Child2D::TopRight,
        ];
        CHILDREN.iter()
    }
}

impl Child for Child2D {
    #[inline]
    fn to_bits(self) -> u64 {
        self as u64
    }
}

/// Helper enum representing a direction from a node.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum NeighbourDirection2D {
    North,
    East,
    South,
    West,
}

impl NeighbourDirection2D {
    /// Helper function to give the opposite direction from a given one. This is used in the
    /// neighbour search for children.
    #[inline]
    pub fn opposite(self) -> Self {
        match self {
            Self::North => Self::South,
            Self::East => Self::West,
            Self::South => Self::North,
            Self::West => Self::East,
        }
    }

    /// Returns an iterator over all possible values.
    #[inline]
    pub fn iter() -> std::slice::Iter<'static, Self> {
        const DIRECTIONS: [NeighbourDirection2D; 4] = [
            NeighbourDirection2D::North,
            NeighbourDirection2D::East,
            NeighbourDirection2D::South,
            NeighbourDirection2D::West,
        ];
        DIRECTIONS.iter()
    }
}

impl LocationalCode2D {
    /// For a given code, returns the codes of the children of the node for the given neighbour direction.
    pub fn neighbour_direction_children_codes(
        self,
        neighbour_direction: NeighbourDirection2D,
    ) -> Option<(Self, Self)> {
        if self.can_have_children() {
            let children = match neighbour_direction {
                NeighbourDirection2D::North => (Child2D::TopLeft, Child2D::TopRight),
                NeighbourDirection2D::East => (Child2D::BottomRight, Child2D::TopRight),
                NeighbourDirection2D::South => (Child2D::BottomLeft, Child2D::BottomRight),
                NeighbourDirection2D::West => (Child2D::BottomLeft, Child2D::TopLeft),
            };
            Some((
                self.child_code(children.0).unwrap(),
                self.child_code(children.1).unwrap(),
            ))
        } else {
            None
        }
    }

    /// For a given code, return the code of the neighbour at the same depth for the given direction.
    /// Returns None if the code is at a boundary and the direction of the neighbour would go outside.
    pub fn same_depth_neighbour(self, neighbour_direction: NeighbourDirection2D) -> Option<Self> {
        // Get depth of the node
        let depth = self.depth();
        // Compute maximum index along an axis for the depth
        let max_index = Self::max_index_for_depth(depth) - 1;
        let raw_code_no_sentinel = Self::unset_msb(self.bits);
        // Decode the code into the 2 coordinates (i, j)
        let coordinates = morton::decode_2d(raw_code_no_sentinel);
        let (new_i, new_j) = match neighbour_direction {
            NeighbourDirection2D::North => {
                if coordinates.1 == max_index {
                    return None;
                } else {
                    (coordinates.0, coordinates.1 + 1)
                }
            }
            NeighbourDirection2D::East => {
                if coordinates.0 == max_index {
                    return None;
                } else {
                    (coordinates.0 + 1, coordinates.1)
                }
            }
            NeighbourDirection2D::South => {
                if coordinates.1 == 0 {
                    return None;
                } else {
                    (coordinates.0, coordinates.1 - 1)
                }
            }
            NeighbourDirection2D::West => {
                if coordinates.0 == 0 {
                    return None;
                } else {
                    (coordinates.0 - 1, coordinates.1)
                }
            }
        };
        Some(Self::new_from_code_and_depth(morton::encode_2d(new_i, new_j), depth).unwrap())
    }
}
