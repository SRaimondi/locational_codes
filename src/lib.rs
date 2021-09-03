#[macro_use]
mod common;
pub mod quadtree;


//
// pub mod quadtree {
//     use super::{helpers, LocationalCodeError};
//
//     /// Helper enum representing the possible children for a quadtree locational code.
//     /// The value is set such that the bits are already the morton codes for a 2x2 grid.
//     #[derive(Copy, Clone, Debug, Eq, PartialEq)]
//     #[repr(u8)]
//     pub enum Child {
//         BottomLeft = 0b00,
//         BottomRight = 0b01,
//         TopLeft = 0b10,
//         TopRight = 0b11,
//     }
//
//     impl Child {
//         /// Return an iterator over all possible values.
//         #[inline]
//         pub fn iter() -> std::slice::Iter<'static, Self> {
//             const CHILDREN: [Child; 4] = [
//                 Child::BottomLeft,
//                 Child::BottomRight,
//                 Child::TopLeft,
//                 Child::TopRight,
//             ];
//             CHILDREN.iter()
//         }
//     }
//
//     /// Helper enum representing a direction from a node.
//     #[derive(Copy, Clone, Debug, Eq, PartialEq)]
//     #[repr(u8)]
//     pub enum NeighbourDirection {
//         North,
//         East,
//         South,
//         West,
//     }
//
//     impl NeighbourDirection {
//         /// Helper function to give the opposite direction from a given one. This is used in the
//         /// neighbour search for children.
//         #[inline]
//         pub fn opposite(self) -> Self {
//             match self {
//                 Self::North => Self::South,
//                 Self::East => Self::West,
//                 Self::South => Self::North,
//                 Self::West => Self::East,
//             }
//         }
//
//         /// Returns an iterator over all possible values.
//         #[inline]
//         pub fn iter() -> std::slice::Iter<'static, Self> {
//             const DIRECTIONS: [NeighbourDirection; 4] = [
//                 NeighbourDirection::North,
//                 NeighbourDirection::East,
//                 NeighbourDirection::South,
//                 NeighbourDirection::West,
//             ];
//             DIRECTIONS.iter()
//         }
//     }
//
//     locational_code_impl!(LocationalCode, 2, Child);
//
//     impl LocationalCode {
//         /// For a given code, returns the codes of the children for the given neighbour direction.
//         #[inline]
//         pub fn neighbour_direction_children_codes(
//             self,
//             neighbour_direction: NeighbourDirection,
//         ) -> Option<(Self, Self)> {
//             if self.can_have_children() {
//                 // Codes are encoded as couple of 2 bits for each direction
//                 // North: shift = 0, TopRight | TopLeft
//                 // East: shift = 4,  TopRight | BottomRight
//                 // South: shift = 8,  BottomRight | BottomLeft
//                 // West: shift = 12,  TopLeft | BottomLeft
//                 const CHILDREN_MASK: u64 = 0b1000_0100_1101_1110;
//                 let children_chunk = (CHILDREN_MASK >> 4 * neighbour_direction as u64) & 0b1111;
//                 Some(unsafe {
//                     (
//                         self.child_code_bits_unchecked(children_chunk & 0b11),
//                         self.child_code_bits_unchecked((children_chunk >> 2) & 0b11),
//                     )
//                 })
//             } else {
//                 None
//             }
//         }
//
//         /// For a given code, return the code of the neighbour at the same depth for the given direction.
//         /// Returns None if the code is at a boundary and the direction of the neighbour would go outside.
//         #[inline]
//         pub fn same_depth_neighbour(self, neighbour_direction: NeighbourDirection) -> Option<Self> {
//             // Get depth of the node
//             let depth = self.depth();
//             // Compute maximum index along an axis for the depth
//             let max_index = Self::max_index_for_depth(depth) - 1;
//             let raw_code_no_sentinel = helpers::unset_msb(self.bits);
//             // Decode the code into the 2 coordinates (i, j)
//             let coordinates = morton::decode_2d(raw_code_no_sentinel);
//             let (new_i, new_j) = match neighbour_direction {
//                 NeighbourDirection::North => {
//                     if coordinates.1 == max_index {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1 + 1)
//                     }
//                 }
//                 NeighbourDirection::East => {
//                     if coordinates.0 == max_index {
//                         return None;
//                     } else {
//                         (coordinates.0 + 1, coordinates.1)
//                     }
//                 }
//                 NeighbourDirection::South => {
//                     if coordinates.1 == 0 {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1 - 1)
//                     }
//                 }
//                 NeighbourDirection::West => {
//                     if coordinates.0 == 0 {
//                         return None;
//                     } else {
//                         (coordinates.0 - 1, coordinates.1)
//                     }
//                 }
//             };
//             Some(unsafe {
//                 Self::new_from_code_and_depth_unchecked(morton::encode_2d(new_i, new_j), depth)
//             })
//         }
//     }
//
//     #[cfg(test)]
//     mod test {
//         use super::*;
//
//         #[test]
//         fn test_max_index_for_depth() {
//             for depth in 0..=LocationalCode::MAX_INCLUSIVE_DEPTH {
//                 assert_eq!(
//                     LocationalCode::max_index_for_depth(depth),
//                     2u32.pow(depth + 1)
//                 );
//             }
//         }
//
//         #[test]
//         fn test_root_creation() {
//             assert_eq!(LocationalCode::new_root(Child::BottomLeft).bits, 0b100);
//             assert_eq!(LocationalCode::new_root(Child::BottomRight).bits, 0b101);
//             assert_eq!(LocationalCode::new_root(Child::TopLeft).bits, 0b110);
//             assert_eq!(LocationalCode::new_root(Child::TopRight).bits, 0b111);
//         }
//
//         #[test]
//         fn test_node_depth() {
//             for d in 0..LocationalCode::MAX_INCLUSIVE_DEPTH {
//                 assert_eq!(
//                     LocationalCode::new_from_code_and_depth(0, d)
//                         .unwrap()
//                         .depth(),
//                     d
//                 );
//             }
//         }
//
//         #[test]
//         fn test_parent_code() {
//             let c = LocationalCode::new_from_code(0b1_11_00_01);
//             let p0 = match c.unwrap().parent_code() {
//                 Some(c) => {
//                     assert_eq!(c.bits, 0b1_11_00);
//                     c
//                 }
//                 None => panic!("Expected parent but code was not found"),
//             };
//             let p1 = match p0.parent_code() {
//                 Some(c) => {
//                     assert_eq!(c.bits, 0b1_11);
//                     c
//                 }
//                 None => panic!("Expected parent but code was not found"),
//             };
//             if p1.parent_code().is_some() {
//                 panic!("Expected code to be a root code");
//             }
//         }
//
//         #[test]
//         fn test_child_code() {
//             let root = LocationalCode::new_root(Child::TopLeft);
//             assert_eq!(root.child_code(Child::BottomLeft).unwrap().bits, 0b1_10_00);
//             assert_eq!(root.child_code(Child::BottomRight).unwrap().bits, 0b1_10_01);
//             assert_eq!(root.child_code(Child::TopLeft).unwrap().bits, 0b1_10_10);
//             assert_eq!(root.child_code(Child::TopRight).unwrap().bits, 0b1_10_11);
//         }
//
//         #[test]
//         fn test_neighbour_code() {
//             // Bottom left root node
//             let node = LocationalCode::new_root(Child::BottomLeft);
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(LocationalCode::new_root(Child::TopLeft))
//             );
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(LocationalCode::new_root(Child::BottomRight))
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//             // Bottom right root node
//             let node = LocationalCode::new_root(Child::BottomRight);
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(LocationalCode::new_root(Child::TopRight))
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(LocationalCode::new_root(Child::BottomLeft))
//             );
//
//             // Top left root node
//             let node = LocationalCode::new_root(Child::TopLeft);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(LocationalCode::new_root(Child::TopRight))
//             );
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(LocationalCode::new_root(Child::BottomLeft))
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//             // Top right root node
//             let node = LocationalCode::new_root(Child::TopRight);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(LocationalCode::new_root(Child::BottomRight))
//             );
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(LocationalCode::new_root(Child::TopLeft))
//             );
//
//             // Test some node at depth 1
//             let node = LocationalCode::new_from_code_and_depth(0b00_11, 1).unwrap();
//             let north = LocationalCode::new_from_code_and_depth(0b10_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(north)
//             );
//             let east = LocationalCode::new_from_code_and_depth(0b01_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(east)
//             );
//             let south = LocationalCode::new_from_code_and_depth(0b00_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(south)
//             );
//             let west = LocationalCode::new_from_code_and_depth(0b00_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(west)
//             );
//
//             let node = LocationalCode::new_from_code_and_depth(0b11_00, 1).unwrap();
//             let north = LocationalCode::new_from_code_and_depth(0b11_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(north)
//             );
//             let east = LocationalCode::new_from_code_and_depth(0b11_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(east)
//             );
//             let south = LocationalCode::new_from_code_and_depth(0b01_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(south)
//             );
//             let west = LocationalCode::new_from_code_and_depth(0b10_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(west)
//             );
//
//             // Test corners
//             let node = LocationalCode::new_from_code_and_depth(0b00_00, 1).unwrap();
//             let north = LocationalCode::new_from_code_and_depth(0b00_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(north)
//             );
//             let east = LocationalCode::new_from_code_and_depth(0b00_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(east)
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//             let node = LocationalCode::new_from_code_and_depth(0b01_01, 1).unwrap();
//             let north = LocationalCode::new_from_code_and_depth(0b01_11, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::North),
//                 Some(north)
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//             let west = LocationalCode::new_from_code_and_depth(0b01_00, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(west)
//             );
//
//             let node = LocationalCode::new_from_code_and_depth(0b10_10, 1).unwrap();
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//             let east = LocationalCode::new_from_code_and_depth(0b10_11, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::East),
//                 Some(east)
//             );
//             let south = LocationalCode::new_from_code_and_depth(0b10_00, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(south)
//             );
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//             let node = LocationalCode::new_from_code_and_depth(0b11_11, 1).unwrap();
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//             assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//             let south = LocationalCode::new_from_code_and_depth(0b11_01, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::South),
//                 Some(south)
//             );
//             let west = LocationalCode::new_from_code_and_depth(0b11_10, 1).unwrap();
//             assert_eq!(
//                 node.same_depth_neighbour(NeighbourDirection::West),
//                 Some(west)
//             );
//         }
//     }
// }

// pub mod octree {
//     use super::{helpers, LocationalCodeError};
//
//     /// Helper enum representing the possible children for an octree locational code.
//     /// The value is set such that the bits are already the morton codes for a 2x2x2 grid.
//     #[derive(Copy, Clone, Debug, Eq, PartialEq)]
//     #[repr(u8)]
//     pub enum Child {
//         BackBottomLeft = 0b000,
//         BackBottomRight = 0b001,
//         BackTopLeft = 0b010,
//         BackTopRight = 0b011,
//         FrontBottomLeft = 0b100,
//         FrontBottomRight = 0b101,
//         FrontTopLeft = 0b110,
//         FrontTopRight = 0b111,
//     }
//
//     impl Child {
//         /// Return an iterator over all possible values.
//         #[inline]
//         pub fn iter() -> std::slice::Iter<'static, Self> {
//             const CHILDREN: [Child; 8] = [
//                 Child::BackBottomLeft,
//                 Child::BackBottomRight,
//                 Child::BackTopLeft,
//                 Child::BackTopRight,
//                 Child::FrontBottomLeft,
//                 Child::FrontBottomRight,
//                 Child::FrontTopLeft,
//                 Child::FrontTopRight,
//             ];
//             CHILDREN.iter()
//         }
//     }
//
//     /// Helper enum representing a direction from a node.
//     #[derive(Copy, Clone, Debug, Eq, PartialEq)]
//     #[repr(u8)]
//     pub enum NeighbourDirection {
//         PositiveX,
//         NegativeX,
//         PositiveY,
//         NegativeY,
//         PositiveZ,
//         NegativeZ,
//     }
//
//     impl NeighbourDirection {
//         /// Helper function to give the opposite direction from a given one. This is used in the
//         /// neighbour search for children.
//         #[inline]
//         pub fn opposite(self) -> Self {
//             match self {
//                 Self::PositiveX => Self::NegativeX,
//                 Self::NegativeX => Self::PositiveX,
//                 Self::PositiveY => Self::NegativeY,
//                 Self::NegativeY => Self::PositiveY,
//                 Self::PositiveZ => Self::NegativeZ,
//                 Self::NegativeZ => Self::PositiveZ,
//             }
//         }
//
//         /// Returns an iterator over all possible values.
//         #[inline]
//         pub fn iter() -> std::slice::Iter<'static, Self> {
//             const DIRECTIONS: [NeighbourDirection; 6] = [
//                 NeighbourDirection::PositiveX,
//                 NeighbourDirection::NegativeX,
//                 NeighbourDirection::PositiveY,
//                 NeighbourDirection::NegativeY,
//                 NeighbourDirection::PositiveZ,
//                 NeighbourDirection::NegativeZ,
//             ];
//             DIRECTIONS.iter()
//         }
//     }
//
//     locational_code_impl!(LocationalCode, 3, Child);
//
//     impl LocationalCode {
//         /// For a given code, returns the codes of the children for the given neighbour direction.
//         #[inline]
//         pub fn neighbour_direction_children_codes(
//             self,
//             neighbour_direction: NeighbourDirection,
//         ) -> Option<(Self, Self, Self, Self)> {
//             if self.can_have_children() {
//                 const CHILDREN_MASKS: [u16; 6] = [
//                     0b111_101_011_001,
//                     0b110_100_010_000,
//                     0b111_110_011_010,
//                     0b101_100_001_000,
//                     0b111_110_101_100,
//                     0b011_010_001_000,
//                 ];
//                 let children = CHILDREN_MASKS[neighbour_direction as usize] as u64;
//                 const CHILD_BITS_MASK: u64 = 0b111;
//                 Some(unsafe {
//                     (
//                         self.child_code_bits_unchecked(children & CHILD_BITS_MASK),
//                         self.child_code_bits_unchecked((children >> 3) & CHILD_BITS_MASK),
//                         self.child_code_bits_unchecked((children >> 6) & CHILD_BITS_MASK),
//                         self.child_code_bits_unchecked((children >> 9) & CHILD_BITS_MASK),
//                     )
//                 })
//             } else {
//                 None
//             }
//         }
//
//         /// For a given code, return the code of the neighbour at the same depth for the given direction.
//         /// Returns None if the code is at a boundary and the direction of the neighbour would go outside.
//         #[inline]
//         pub fn same_depth_neighbour(self, neighbour_direction: NeighbourDirection) -> Option<Self> {
//             // Get depth of the node
//             let depth = self.depth();
//             // Compute maximum index along an axis for the depth
//             let max_index = Self::max_index_for_depth(depth) - 1;
//             let raw_code_no_sentinel = helpers::unset_msb(self.bits);
//             // Decode the code into the 3 coordinates (i, j, k)
//             let coordinates = morton::decode_3d(raw_code_no_sentinel);
//             let (new_i, new_j, new_k) = match neighbour_direction {
//                 NeighbourDirection::PositiveX => {
//                     if coordinates.0 == max_index {
//                         return None;
//                     } else {
//                         (coordinates.0 + 1, coordinates.1, coordinates.2)
//                     }
//                 }
//                 NeighbourDirection::NegativeX => {
//                     if coordinates.0 == 0 {
//                         return None;
//                     } else {
//                         (coordinates.0 - 1, coordinates.1, coordinates.2)
//                     }
//                 }
//                 NeighbourDirection::PositiveY => {
//                     if coordinates.1 == max_index {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1 + 1, coordinates.2)
//                     }
//                 }
//                 NeighbourDirection::NegativeY => {
//                     if coordinates.1 == 0 {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1 - 1, coordinates.2)
//                     }
//                 }
//                 NeighbourDirection::PositiveZ => {
//                     if coordinates.2 == max_index {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1, coordinates.2 + 1)
//                     }
//                 }
//                 NeighbourDirection::NegativeZ => {
//                     if coordinates.2 == 0 {
//                         return None;
//                     } else {
//                         (coordinates.0, coordinates.1, coordinates.2 - 1)
//                     }
//                 }
//             };
//
//             let mc = match morton::encode_3d(new_i, new_j, new_k) {
//                 morton::Encoded3DCode::AllBits(m) => m,
//                 morton::Encoded3DCode::SomeBits(_) => {
//                     panic!("Discarded some bits during neighbour code composition")
//                 }
//             };
//
//             Some(unsafe { Self::new_from_code_and_depth_unchecked(mc, depth) })
//         }
//     }
// }
