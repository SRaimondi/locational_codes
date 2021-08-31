/// Find the index of the most significant bit, fails in debug if the value is 0.
#[inline]
pub fn msb_index(v: u64) -> u32 {
    debug_assert_ne!(v, 0);
    u64::BITS - 1 - v.leading_zeros()
}

/// Set the most significant bit to 0, fails in debug if the value is 0.
#[inline]
pub fn unset_msb(v: u64) -> u64 {
    v ^ (1 << msb_index(v))
}

/// Helper function that adds the sentinel bit to a given raw code for the given depth.
/// Checks the code only in debug mode.
#[inline]
pub fn add_sentinel_bit(code: u64, depth: u32, per_level_bits: u32) -> u64 {
    let sentinel_index = (depth + 1) * per_level_bits;
    let sentinel_mask = 1 << sentinel_index;
    debug_assert!(code < sentinel_mask);
    code | sentinel_mask
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_msb_index() {
        for i in 0..63 {
            assert_eq!(msb_index(1 << i), i);
        }
    }

    #[test]
    fn test_unset_msb() {
        for i in 0..63 {
            assert_eq!(unset_msb(1 << i), 0);
        }
    }

    #[test]
    fn test_add_sentinel_bit() {
        const PER_LEVEL_BITS: u32 = 2;
        for depth in 0..=30 {
            assert_eq!(
                add_sentinel_bit(0, depth, PER_LEVEL_BITS),
                1 << ((depth + 1) * PER_LEVEL_BITS)
            );
        }
    }
}
