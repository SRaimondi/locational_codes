use crate::lc::helpers;

#[derive(Copy, Clone, Debug)]
pub enum LocationalCodeError {
    InvalidRawCode,
    InvalidDepth,
}

pub trait LocationalCodeBase: Copy + std::convert::Into<u64> {
    /// Number of bits used to represent each level of the code (2 for 2D, 3 for 3D).
    const PER_LEVEL_BITS: u32;
    /// Maximum inclusive depth the code can represent for the bits we use at each level.
    const MAX_INCLUSIVE_DEPTH: u32 = (u64::BITS - 1) / Self::PER_LEVEL_BITS - 1;
    /// Smallest valid code.
    const SMALLEST_CODE: u64 = 1 << Self::PER_LEVEL_BITS;
    /// Largest valid code.
    const LARGEST_CODE: u64 = (1 << (Self::MAX_INCLUSIVE_DEPTH * Self::PER_LEVEL_BITS + 1)) - 1;

    /// Create a new LC from the given raw code by trusting it's valid.
    unsafe fn new_from_raw(code: u64) -> Self;

    /// Create a new LC from the given code, check that the given value is within the valid range
    /// of the LC.
    fn new_from_code(code: u64) -> Result<Self, LocationalCodeError> {
        if (Self::SMALLEST_CODE..=Self::LARGEST_CODE).contains(&code) {
            Ok(unsafe { Self::new_from_raw(code) })
        } else {
            Err(LocationalCodeError::InvalidRawCode)
        }
    }

    /// Create a new LC from the given code and depth by adding the sentinel bit. Checks that the
    /// depth is valid and the code is in a valid range after adding the sentinel bit.
    fn new_from_code_and_depth(code: u64, depth: u32) -> Result<Self, LocationalCodeError> {
        if depth <= Self::MAX_INCLUSIVE_DEPTH {
            Self::new_from_code(helpers::add_sentinel_bit(code, depth, Self::PER_LEVEL_BITS))
        } else {
            Err(LocationalCodeError::InvalidDepth)
        }
    }

    /// Computes the maximum index along a single axis. Equals to 2^(depth + 1).
    /// Panics if the given depth is larger than the maximum for the LC.
    #[inline]
    fn max_index_for_depth(depth: u32) -> u32 {
        assert!(depth <= Self::MAX_INCLUSIVE_DEPTH);
        1 << (depth + 1)
    }

    /// Computes the depth of the code starting from 0.
    #[inline]
    fn depth(self) -> u32 {
        helpers::msb_index(self.into()) / Self::PER_LEVEL_BITS - 1
    }

    /// Computes the LC of the parent. We call the unsafe constructor here as we trust that the
    /// code used in the call is a valid one.
    #[inline]
    fn parent_code(self) -> Option<Self> {
        if helpers::msb_index(self.into()) == Self::PER_LEVEL_BITS {
            None
        } else {
            // The parent code is simply computed by removing the bits of the current level
            Some(unsafe { Self::new_from_raw(self.into() >> Self::PER_LEVEL_BITS) })
        }
    }

    // Compute the LC of the child code without checking if self can have children.
    #[inline]
    unsafe fn child_code_unchecked<T>(self, child: T) -> Self
    where
        T: std::convert::Into<u64>,
    {
        Self::new_from_raw((self.into() << Self::PER_LEVEL_BITS) | child.into())
    }

    /// Compute the LC of the child code for a type that can be converted to u64.
    #[inline]
    fn child_code<T>(self, child: T) -> Option<Self>
    where
        T: std::convert::Into<u64>,
    {
        if self.can_have_children() {
            Some(unsafe { self.child_code_unchecked(child) })
        } else {
            None
        }
    }

    /// Checks if a code can have children codes.
    #[inline]
    fn can_have_children(self) -> bool {
        self.depth() < Self::MAX_INCLUSIVE_DEPTH
    }
}
