// use crate::lc::{common::LocationalCodeBase, helpers};
//
// /// Helper enum representing the possible children in a node. The value is set such that the bits
// /// are already the morton codes for a 2x2 grid.
// #[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[repr(u8)]
// pub enum Child3D {
//     BackBottomLeft = 0b000,
//     BackBottomRight = 0b001,
//     BackTopLeft = 0b010,
//     BackTopRight = 0b011,
//     FrontBottomLeft = 0b100,
//     FrontBottomRight = 0b101,
//     FrontTopLeft = 0b110,
//     FrontTopRight = 0b111,
// }
//
// impl std::convert::Into<u64> for Child3D {
//     #[inline]
//     fn into(self) -> u64 {
//         self as u64
//     }
// }
//
// impl Child3D {
//     /// Return an iterator over all possible values.
//     #[inline]
//     pub fn iter() -> std::slice::Iter<'static, Self> {
//         const CHILDREN: [Child3D; 8] = [
//             Child3D::BackBottomLeft,
//             Child3D::BackBottomRight,
//             Child3D::BackTopLeft,
//             Child3D::BackTopRight,
//             Child3D::FrontBottomLeft,
//             Child3D::FrontBottomRight,
//             Child3D::FrontTopLeft,
//             Child3D::FrontTopRight,
//         ];
//         CHILDREN.iter()
//     }
// }
//
// /// Helper enum representing a direction from a node.
// #[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[repr(u8)]
// pub enum NeighbourDirection3D {
//     PositiveX,
//     NegativeX,
//     PositiveY,
//     NegativeY,
//     PositiveZ,
//     NegativeZ,
// }
//
// impl NeighbourDirection3D {
//     /// Helper function to give the opposite direction from a given one. This is used in the
//     /// neighbour search for children.
//     #[inline]
//     pub fn opposite(self) -> Self {
//         match self {
//             Self::PositiveX => Self::NegativeX,
//             Self::NegativeX => Self::PositiveX,
//             Self::PositiveY => Self::NegativeY,
//             Self::NegativeY => Self::PositiveY,
//             Self::PositiveZ => Self::NegativeZ,
//             Self::NegativeZ => Self::PositiveZ,
//         }
//     }
//
//     /// Returns an iterator over all possible values.
//     #[inline]
//     pub fn iter() -> std::slice::Iter<'static, Self> {
//         const DIRECTIONS: [NeighbourDirection3D; 6] = [
//             NeighbourDirection3D::PositiveX,
//             NeighbourDirection3D::NegativeX,
//             NeighbourDirection3D::PositiveY,
//             NeighbourDirection3D::NegativeY,
//             NeighbourDirection3D::PositiveZ,
//             NeighbourDirection3D::NegativeZ,
//         ];
//         DIRECTIONS.iter()
//     }
// }
//
// /// Struct representing a locational code for the 3D case.
// #[derive(Copy, Clone, Eq, PartialEq, Hash)]
// pub struct LocationalCode3D {
//     internal: u64,
// }
//
// impl std::convert::Into<u64> for LocationalCode3D {
//     #[inline]
//     fn into(self) -> u64 {
//         self.internal
//     }
// }
//
// impl std::fmt::Debug for LocationalCode3D {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "LocationalCode3D: 0b{:b}", self.internal)
//     }
// }
//
// impl LocationalCode3D {
//     /// Create new LC representing a root node.
//     #[inline]
//     pub const fn new_root(child: Child3D) -> Self {
//         const ROOT_SENTINEL_MASK: u64 = 0b1000;
//         Self {
//             internal: ROOT_SENTINEL_MASK | child as u64,
//         }
//     }
// }
//
// impl LocationalCodeBase for LocationalCode3D {
//     const PER_LEVEL_BITS: u32 = 3;
//
//     #[inline]
//     unsafe fn new_from_code_unchecked(code: u64) -> Self {
//         debug_assert!((Self::SMALLEST_CODE..=Self::LARGEST_CODE).contains(&code));
//         Self { internal: code }
//     }
// }
