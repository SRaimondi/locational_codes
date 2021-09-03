pub mod helpers {
    /// Helper function to find the index of the most significant bit. Assumes the value is not 0.
    #[inline]
    pub fn msb_index(v: u64) -> u32 {
        debug_assert!(v != 0);
        u64::BITS - 1 - v.leading_zeros()
    }

    /// Set the most significant bit to 0. Assumes the value is not 0.
    #[inline]
    pub fn unset_msb(v: u64) -> u64 {
        v ^ (1 << msb_index(v))
    }

    #[cfg(test)]
    mod test {
        use super::*;

        #[test]
        fn test_msb_index() {
            for i in 0..64 {
                assert_eq!(msb_index(1 << i), i);
            }
            assert_eq!(msb_index(0b1111), 3);
            assert_eq!(msb_index(0b101111), 5);
        }

        #[test]
        fn test_unset_msb() {
            for i in 0..64 {
                assert_eq!(unset_msb(1 << i), 0);
            }
            assert_eq!(unset_msb(0b1111), 0b111);
            assert_eq!(unset_msb(0b101111), 0b1111);
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LocationalCodeError {
    InvalidCodeWithSentinel,
    InvalidCodeWithoutSentinel,
    InvalidDepth,
    InvalidChildBits,
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
            #[inline]
            fn is_valid_code_without_sentinel(code: u64) -> bool {
                const MAX: u64 = (1 << ($name::MAX_INCLUSIVE_DEPTH + 1) * $lvl_bits) - 1;
                (0..=MAX).contains(&code)
            }

            /// Helper function to check if a code is in the valid range.
            #[inline]
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
            #[inline]
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

            /// Create new locational code as root code for the given node child.
            #[inline]
            pub fn new_root(child: $child) -> Self {
                Self {
                    bits: (1 << $lvl_bits) | child as u64,
                }
            }

            /// Create a new locational code from the given raw code.
            /// # Safety
            /// The code is expected to be valid as there is no check on it for this constructor.
            #[inline]
            pub unsafe fn new_from_code_unchecked(code: u64) -> Self {
                debug_assert!(Self::is_valid_code(code));
                Self { bits: code }
            }

            /// Create a new locational code from the given code, check that the given value is within the
            /// valid range.
            #[inline]
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
            #[inline]
            pub unsafe fn new_from_code_and_depth_unchecked(code: u64, depth: u32) -> Self {
                Self::new_from_code_unchecked(Self::add_sentinel_bit(code, depth))
            }

            /// Create a new locational code from the given code and depth. Checks both the code
            /// and the depth to be valid.
            #[inline]
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

            /// Compute the locational code of the child using the given bits.
            /// # Safety
            /// The caller is responsible for ensuring that ```self``` can have children and
            /// the given bits to compute the child are in a valid range.
            #[inline]
            pub unsafe fn child_code_bits_unchecked(self, child_bits: u64) -> Self {
                debug_assert!(child_bits < (1 << $lvl_bits));
                Self::new_from_code_unchecked((self.bits << $lvl_bits) | child_bits)
            }

            /// Compute the locational code of the child for the given child bits. Returns an error
            /// if the bits are larger than the maximum allowed.
            #[inline]
            pub fn child_code_bits(self, child_bits: u64) -> Result<Self, LocationalCodeError> {
                if child_bits < (1 << $lvl_bits) {
                    Ok(unsafe { self.child_code_bits_unchecked(child_bits) })
                } else {
                    Err(LocationalCodeError::InvalidChildBits)
                }
            }

            /// Compute the locational code of the child without checking if self can have children.
            /// # Safety
            /// The caller must be sure it's possible to compute a child code without loss of bits.
            #[inline]
            pub unsafe fn child_code_unchecked(self, child: $child) -> Self {
                self.child_code_bits_unchecked(child as u64)
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

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "LocationalCode: 0b{:b}", self.bits)
            }
        }
    };
}