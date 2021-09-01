mod helpers {
    /// Helper function to find the index of the most significant bit.
    #[inline]
    pub const fn msb_index(v: u64) -> u32 {
        u64::BITS - 1 - v.leading_zeros()
    }

    /// Set the most significant bit to 0.
    #[inline]
    pub const fn unset_msb(v: u64) -> u64 {
        v ^ (1 << msb_index(v))
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LocationalCodeError {
    InvalidCodeWithSentinel,
    InvalidCodeWithoutSentinel,
    InvalidDepth,
}

macro_rules! locational_code_impl {
    ($name:ident, $lvl_bits:expr, $child:ty) => {
        #[derive(Copy, Clone, Eq, PartialEq, Hash)]
        pub struct $name {
            bits: u64,
        }

        impl $name {
            /// Maximum inclusive depth the code can represent for the bits we use at each level.
            pub const MAX_INCLUSIVE_DEPTH: u32 = (u64::BITS - 1) / $lvl_bits - 1;

            /// Helper function to check that a code without the sentinel is in the valid range.
            fn is_valid_code_without_sentinel(code: u64) -> bool {
                const MAX: u64 = (1 << ($name::MAX_INCLUSIVE_DEPTH + 1) * $lvl_bits) - 1;
                (0..=MAX).contains(&code)
            }

            /// Helper function to check if a code is in the valid range.
            fn is_valid_code(code: u64) -> bool {
                const MIN: u64 = 1 << $lvl_bits;
                const MAX_USED_BITS: u32 = ($name::MAX_INCLUSIVE_DEPTH + 1) * $lvl_bits + 1;
                const MAX: u64 = if MAX_USED_BITS == u64::BITS {
                    u64::MAX
                } else {
                    (1 << (($name::MAX_INCLUSIVE_DEPTH + 1) * $lvl_bits + 1)) - 1
                };
                (MIN..=MAX).contains(&code)
            }

            /// Helper function to check if a depth is valid.
            fn is_valid_depth(depth: u32) -> bool {
                depth <= $name::MAX_INCLUSIVE_DEPTH
            }

            /// Helper function that adds the sentinel bit to a given raw code for the given depth.
            /// Panics in debug mode if the code or the depth are invalid.
            #[inline]
            fn add_sentinel_bit(code: u64, depth: u32) -> u64 {
                debug_assert!(Self::is_valid_code_without_sentinel(code));
                debug_assert!(Self::is_valid_depth(depth));
                let sentinel_index = (depth + 1) * $lvl_bits;
                let sentinel_mask = 1 << sentinel_index;
                debug_assert!(code < sentinel_mask);
                code | sentinel_mask
            }

            /// Computes the maximum index along a single axis. Equals to 2^(depth + 1).
            /// Panics if the given depth is larger than the maximum allowed.
            #[inline]
            pub fn max_index_for_depth(depth: u32) -> u32 {
                assert!(Self::is_valid_depth(depth));
                1 << (depth + 1)
            }

            pub fn new_root(child: $child) -> Self {
                Self {
                    bits: (1 << $lvl_bits) | child as u64,
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
            pub fn new_from_code_and_depth(
                code: u64,
                depth: u32,
            ) -> Result<Self, LocationalCodeError> {
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
                helpers::msb_index(self.bits) / $lvl_bits - 1
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
                if helpers::msb_index(self.bits) == $lvl_bits {
                    None
                } else {
                    // The parent code is simply computed by removing the bits of the current level
                    Some(unsafe { Self::new_from_code_unchecked(self.bits >> $lvl_bits) })
                }
            }

            /// Compute the locational code of the child without checking if self can have children.
            /// # Safety
            /// The caller must be sure it's possible to compute a child code without loss of bits.
            #[inline]
            pub unsafe fn child_code_unchecked(self, child: $child) -> Self {
                Self::new_from_code_unchecked((self.bits << $lvl_bits) | child as u64)
            }

            /// Compute the LC of the child code for a type that can be converted to u64.
            #[inline]
            pub fn child_code(self, child: $child) -> Option<Self> {
                if self.can_have_children() {
                    Some(unsafe { self.child_code_unchecked(child) })
                } else {
                    None
                }
            }
        }

        impl std::fmt::Debug for LocationalCode {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}: 0b{:b}", stringify!($name), self.bits)
            }
        }
    };
}

pub mod quadtree {
    use super::{helpers, LocationalCodeError};

    /// Helper enum representing the possible children for a quadtree locational code.
    /// The value is set such that the bits are already the morton codes for a 2x2 grid.
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    #[repr(u8)]
    pub enum Child {
        BottomLeft = 0b00,
        BottomRight = 0b01,
        TopLeft = 0b10,
        TopRight = 0b11,
    }

    impl Child {
        /// Return an iterator over all possible values.
        #[inline]
        pub fn iter() -> std::slice::Iter<'static, Self> {
            const CHILDREN: [Child; 4] = [
                Child::BottomLeft,
                Child::BottomRight,
                Child::TopLeft,
                Child::TopRight,
            ];
            CHILDREN.iter()
        }
    }

    /// Helper enum representing a direction from a node.
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    #[repr(u8)]
    pub enum NeighbourDirection {
        North,
        East,
        South,
        West,
    }

    impl NeighbourDirection {
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
            const DIRECTIONS: [NeighbourDirection; 4] = [
                NeighbourDirection::North,
                NeighbourDirection::East,
                NeighbourDirection::South,
                NeighbourDirection::West,
            ];
            DIRECTIONS.iter()
        }
    }

    locational_code_impl!(LocationalCode, 2, Child);

    impl LocationalCode {
        /// For a given code, returns the codes of the children of the node for the given neighbour direction.
        pub fn neighbour_direction_children_codes(
            self,
            neighbour_direction: NeighbourDirection,
        ) -> Option<(Self, Self)> {
            if self.can_have_children() {
                let children = match neighbour_direction {
                    NeighbourDirection::North => (Child::TopLeft, Child::TopRight),
                    NeighbourDirection::East => (Child::BottomRight, Child::TopRight),
                    NeighbourDirection::South => (Child::BottomLeft, Child::BottomRight),
                    NeighbourDirection::West => (Child::BottomLeft, Child::TopLeft),
                };
                Some(unsafe {
                    (
                        self.child_code_unchecked(children.0),
                        self.child_code_unchecked(children.1),
                    )
                })
            } else {
                None
            }
        }

        /// For a given code, return the code of the neighbour at the same depth for the given direction.
        /// Returns None if the code is at a boundary and the direction of the neighbour would go outside.
        pub fn same_depth_neighbour(self, neighbour_direction: NeighbourDirection) -> Option<Self> {
            // Get depth of the node
            let depth = self.depth();
            // Compute maximum index along an axis for the depth
            let max_index = Self::max_index_for_depth(depth) - 1;
            let raw_code_no_sentinel = helpers::unset_msb(self.bits);
            // Decode the code into the 2 coordinates (i, j)
            let coordinates = morton::decode_2d(raw_code_no_sentinel);
            let (new_i, new_j) = match neighbour_direction {
                NeighbourDirection::North => {
                    if coordinates.1 == max_index {
                        return None;
                    } else {
                        (coordinates.0, coordinates.1 + 1)
                    }
                }
                NeighbourDirection::East => {
                    if coordinates.0 == max_index {
                        return None;
                    } else {
                        (coordinates.0 + 1, coordinates.1)
                    }
                }
                NeighbourDirection::South => {
                    if coordinates.1 == 0 {
                        return None;
                    } else {
                        (coordinates.0, coordinates.1 - 1)
                    }
                }
                NeighbourDirection::West => {
                    if coordinates.0 == 0 {
                        return None;
                    } else {
                        (coordinates.0 - 1, coordinates.1)
                    }
                }
            };
            Some(unsafe {
                Self::new_from_code_and_depth_unchecked(morton::encode_2d(new_i, new_j), depth)
            })
        }
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_max_index_for_depth() {
            for depth in 0..=LocationalCode::MAX_INCLUSIVE_DEPTH {
                assert_eq!(
                    LocationalCode::max_index_for_depth(depth),
                    2u32.pow(depth + 1)
                );
            }
        }

        #[test]
        fn test_root_creation() {
            assert_eq!(LocationalCode::new_root(Child::BottomLeft).bits, 0b100);
            assert_eq!(LocationalCode::new_root(Child::BottomRight).bits, 0b101);
            assert_eq!(LocationalCode::new_root(Child::TopLeft).bits, 0b110);
            assert_eq!(LocationalCode::new_root(Child::TopRight).bits, 0b111);
        }

        #[test]
        fn test_node_depth() {
            for d in 0..LocationalCode::MAX_INCLUSIVE_DEPTH {
                assert_eq!(
                    LocationalCode::new_from_code_and_depth(0, d)
                        .unwrap()
                        .depth(),
                    d
                );
            }
        }

        #[test]
        fn test_parent_code() {
            let c = LocationalCode::new_from_code(0b1_11_00_01);
            let p0 = match c.unwrap().parent_code() {
                Some(c) => {
                    assert_eq!(c.bits, 0b1_11_00);
                    c
                }
                None => panic!("Expected parent but code was not found"),
            };
            let p1 = match p0.parent_code() {
                Some(c) => {
                    assert_eq!(c.bits, 0b1_11);
                    c
                }
                None => panic!("Expected parent but code was not found"),
            };
            if p1.parent_code().is_some() {
                panic!("Expected code to be a root code");
            }
        }

        #[test]
        fn test_child_code() {
            let root = LocationalCode::new_root(Child::TopLeft);
            assert_eq!(root.child_code(Child::BottomLeft).unwrap().bits, 0b1_10_00);
            assert_eq!(root.child_code(Child::BottomRight).unwrap().bits, 0b1_10_01);
            assert_eq!(root.child_code(Child::TopLeft).unwrap().bits, 0b1_10_10);
            assert_eq!(root.child_code(Child::TopRight).unwrap().bits, 0b1_10_11);
        }

        #[test]
        fn test_neighbour_code() {
            // Bottom left root node
            let node = LocationalCode::new_root(Child::BottomLeft);
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(LocationalCode::new_root(Child::TopLeft))
            );
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(LocationalCode::new_root(Child::BottomRight))
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);

            // Bottom right root node
            let node = LocationalCode::new_root(Child::BottomRight);
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(LocationalCode::new_root(Child::TopRight))
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(LocationalCode::new_root(Child::BottomLeft))
            );

            // Top left root node
            let node = LocationalCode::new_root(Child::TopLeft);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(LocationalCode::new_root(Child::TopRight))
            );
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(LocationalCode::new_root(Child::BottomLeft))
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);

            // Top right root node
            let node = LocationalCode::new_root(Child::TopRight);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(LocationalCode::new_root(Child::BottomRight))
            );
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(LocationalCode::new_root(Child::TopLeft))
            );

            // Test some node at depth 1
            let node = LocationalCode::new_from_code_and_depth(0b00_11, 1).unwrap();
            let north = LocationalCode::new_from_code_and_depth(0b10_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(north)
            );
            let east = LocationalCode::new_from_code_and_depth(0b01_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(east)
            );
            let south = LocationalCode::new_from_code_and_depth(0b00_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(south)
            );
            let west = LocationalCode::new_from_code_and_depth(0b00_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(west)
            );

            let node = LocationalCode::new_from_code_and_depth(0b11_00, 1).unwrap();
            let north = LocationalCode::new_from_code_and_depth(0b11_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(north)
            );
            let east = LocationalCode::new_from_code_and_depth(0b11_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(east)
            );
            let south = LocationalCode::new_from_code_and_depth(0b01_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(south)
            );
            let west = LocationalCode::new_from_code_and_depth(0b10_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(west)
            );

            // Test corners
            let node = LocationalCode::new_from_code_and_depth(0b00_00, 1).unwrap();
            let north = LocationalCode::new_from_code_and_depth(0b00_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(north)
            );
            let east = LocationalCode::new_from_code_and_depth(0b00_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(east)
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);

            let node = LocationalCode::new_from_code_and_depth(0b01_01, 1).unwrap();
            let north = LocationalCode::new_from_code_and_depth(0b01_11, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::North),
                Some(north)
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
            let west = LocationalCode::new_from_code_and_depth(0b01_00, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(west)
            );

            let node = LocationalCode::new_from_code_and_depth(0b10_10, 1).unwrap();
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
            let east = LocationalCode::new_from_code_and_depth(0b10_11, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::East),
                Some(east)
            );
            let south = LocationalCode::new_from_code_and_depth(0b10_00, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(south)
            );
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);

            let node = LocationalCode::new_from_code_and_depth(0b11_11, 1).unwrap();
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
            assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
            let south = LocationalCode::new_from_code_and_depth(0b11_01, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::South),
                Some(south)
            );
            let west = LocationalCode::new_from_code_and_depth(0b11_10, 1).unwrap();
            assert_eq!(
                node.same_depth_neighbour(NeighbourDirection::West),
                Some(west)
            );
        }
    }
}

pub mod octree {
    use super::{helpers, LocationalCodeError};

    /// Helper enum representing the possible children for an octree locational code.
    /// The value is set such that the bits are already the morton codes for a 2x2x2 grid.
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    #[repr(u8)]
    pub enum Child {
        BackBottomLeft = 0b000,
        BackBottomRight = 0b001,
        BackTopLeft = 0b010,
        BackTopRight = 0b011,
        FrontBottomLeft = 0b100,
        FrontBottomRight = 0b101,
        FrontTopLeft = 0b110,
        FrontTopRight = 0b111,
    }

    impl Child {
        /// Return an iterator over all possible values.
        #[inline]
        pub fn iter() -> std::slice::Iter<'static, Self> {
            const CHILDREN: [Child; 8] = [
                Child::BackBottomLeft,
                Child::BackBottomRight,
                Child::BackTopLeft,
                Child::BackTopRight,
                Child::FrontBottomLeft,
                Child::FrontBottomRight,
                Child::FrontTopLeft,
                Child::FrontTopRight,
            ];
            CHILDREN.iter()
        }
    }

    /// Helper enum representing a direction from a node.
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    #[repr(u8)]
    pub enum NeighbourDirection {
        PositiveX,
        NegativeX,
        PositiveY,
        NegativeY,
        PositiveZ,
        NegativeZ,
    }

    impl NeighbourDirection {
        /// Helper function to give the opposite direction from a given one. This is used in the
        /// neighbour search for children.
        #[inline]
        pub fn opposite(self) -> Self {
            match self {
                Self::PositiveX => Self::NegativeX,
                Self::NegativeX => Self::PositiveX,
                Self::PositiveY => Self::NegativeY,
                Self::NegativeY => Self::PositiveY,
                Self::PositiveZ => Self::NegativeZ,
                Self::NegativeZ => Self::PositiveZ,
            }
        }

        /// Returns an iterator over all possible values.
        #[inline]
        pub fn iter() -> std::slice::Iter<'static, Self> {
            const DIRECTIONS: [NeighbourDirection; 6] = [
                NeighbourDirection::PositiveX,
                NeighbourDirection::NegativeX,
                NeighbourDirection::PositiveY,
                NeighbourDirection::NegativeY,
                NeighbourDirection::PositiveZ,
                NeighbourDirection::NegativeZ,
            ];
            DIRECTIONS.iter()
        }
    }

    locational_code_impl!(LocationalCode, 3, Child);
}
