// use crate::lc::{common::LocationalCodeBase, helpers};
//
// /// Helper enum representing the possible children in a node. The value is set such that the bits
// /// are already the morton codes for a 2x2 grid.
// #[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[repr(u8)]
// pub enum Child {
//     BottomLeft = 0b00,
//     BottomRight = 0b01,
//     TopLeft = 0b10,
//     TopRight = 0b11,
// }
//
// impl std::convert::Into<u64> for Child {
//     #[inline]
//     fn into(self) -> u64 {
//         self as u64
//     }
// }
//
// impl Child {
//     /// Return an iterator over all possible values.
//     #[inline]
//     pub fn iter() -> std::slice::Iter<'static, Self> {
//         const CHILDREN: [Child; 4] = [
//             Child::BottomLeft,
//             Child::BottomRight,
//             Child::TopLeft,
//             Child::TopRight,
//         ];
//         CHILDREN.iter()
//     }
// }
//
// /// Helper enum representing a direction from a node.
// #[derive(Copy, Clone, Debug, Eq, PartialEq)]
// #[repr(u8)]
// pub enum NeighbourDirection {
//     North,
//     East,
//     South,
//     West,
// }
//
// impl NeighbourDirection {
//     /// Helper function to give the opposite direction from a given one. This is used in the
//     /// neighbour search for children.
//     #[inline]
//     pub fn opposite(self) -> Self {
//         match self {
//             Self::North => Self::South,
//             Self::East => Self::West,
//             Self::South => Self::North,
//             Self::West => Self::East,
//         }
//     }
//
//     /// Returns an iterator over all possible values.
//     #[inline]
//     pub fn iter() -> std::slice::Iter<'static, Self> {
//         const DIRECTIONS: [NeighbourDirection; 4] = [
//             NeighbourDirection::North,
//             NeighbourDirection::East,
//             NeighbourDirection::South,
//             NeighbourDirection::West,
//         ];
//         DIRECTIONS.iter()
//     }
// }
//
// /// Struct representing a locational code for the 2D case.
// #[derive(Copy, Clone, Eq, PartialEq, Hash)]
// pub struct LocationalCode2D {
//     internal: u64,
// }
//
// impl std::convert::Into<u64> for LocationalCode2D {
//     #[inline]
//     fn into(self) -> u64 {
//         self.internal
//     }
// }
//
// impl std::fmt::Debug for LocationalCode2D {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(f, "LocationalCode2D: 0b{:b}", self.internal)
//     }
// }
//
// impl LocationalCode2D {
//     /// Create new LC representing a root node.
//     #[inline]
//     pub const fn new_root(child: Child) -> Self {
//         const ROOT_SENTINEL_MASK: u64 = 0b100;
//         Self {
//             internal: ROOT_SENTINEL_MASK | child as u64,
//         }
//     }
//
//     /// For a given code, returns the codes of the children of the node for the given neighbour direction.
//     pub fn neighbour_direction_children_codes(
//         self,
//         neighbour_direction: NeighbourDirection,
//     ) -> Option<(Self, Self)> {
//         if self.can_have_children() {
//             let children = match neighbour_direction {
//                 NeighbourDirection::North => (Child::TopLeft, Child::TopRight),
//                 NeighbourDirection::East => (Child::BottomRight, Child::TopRight),
//                 NeighbourDirection::South => (Child::BottomLeft, Child::BottomRight),
//                 NeighbourDirection::West => (Child::BottomLeft, Child::TopLeft),
//             };
//             Some((
//                 self.child_code(children.0).unwrap(),
//                 self.child_code(children.1).unwrap(),
//             ))
//         } else {
//             None
//         }
//     }
//
//     /// For a given code, return the code of the neighbour at the same depth for the given direction.
//     /// Returns None if the code is at a boundary and the direction of the neighbour would go outside.
//     pub fn same_depth_neighbour(self, neighbour_direction: NeighbourDirection) -> Option<Self> {
//         // Get depth of the node
//         let depth = self.depth();
//         // Compute maximum index along an axis for the depth
//         let max_index = Self::max_index_for_depth(depth) - 1;
//         let raw_code_no_sentinel = helpers::unset_msb(self.internal);
//         // Decode the code into the 2 coordinates (i, j)
//         let coordinates = morton::decode_2d(raw_code_no_sentinel);
//         let (new_i, new_j) = match neighbour_direction {
//             NeighbourDirection::North => {
//                 if coordinates.1 == max_index {
//                     return None;
//                 } else {
//                     (coordinates.0, coordinates.1 + 1)
//                 }
//             }
//             NeighbourDirection::East => {
//                 if coordinates.0 == max_index {
//                     return None;
//                 } else {
//                     (coordinates.0 + 1, coordinates.1)
//                 }
//             }
//             NeighbourDirection::South => {
//                 if coordinates.1 == 0 {
//                     return None;
//                 } else {
//                     (coordinates.0, coordinates.1 - 1)
//                 }
//             }
//             NeighbourDirection::West => {
//                 if coordinates.0 == 0 {
//                     return None;
//                 } else {
//                     (coordinates.0 - 1, coordinates.1)
//                 }
//             }
//         };
//         Some(Self::new_from_code_and_depth(morton::encode_2d(new_i, new_j), depth).unwrap())
//     }
// }
//
// impl LocationalCodeBase for LocationalCode2D {
//     const PER_LEVEL_BITS: u32 = 2;
//
//     #[inline]
//     unsafe fn new_from_code_unchecked(code: u64) -> Self {
//         debug_assert!((Self::SMALLEST_CODE..=Self::LARGEST_CODE).contains(&code));
//         Self { internal: code }
//     }
// }
//
// #[cfg(test)]
// mod test {
//     use super::*;
//
//     #[test]
//     fn test_root_creation() {
//         assert_eq!(
//             LocationalCode2D::new_root(Child::BottomLeft).internal,
//             0b100
//         );
//         assert_eq!(
//             LocationalCode2D::new_root(Child::BottomRight).internal,
//             0b101
//         );
//         assert_eq!(LocationalCode2D::new_root(Child::TopLeft).internal, 0b110);
//         assert_eq!(
//             LocationalCode2D::new_root(Child::TopRight).internal,
//             0b111
//         );
//     }
//
//     #[test]
//     fn test_node_depth() {
//         for d in 0..LocationalCode2D::MAX_INCLUSIVE_DEPTH {
//             assert_eq!(
//                 LocationalCode2D::new_from_code_and_depth(0, d)
//                     .unwrap()
//                     .depth(),
//                 d
//             );
//         }
//     }
//
//     #[test]
//     fn test_parent_code() {
//         let c = LocationalCode2D::new_from_code(0b1_11_00_01);
//         let p0 = match c.unwrap().parent_code() {
//             Some(c) => {
//                 assert_eq!(c.internal, 0b1_11_00);
//                 c
//             }
//             None => panic!("Expected parent but code was not found"),
//         };
//         let p1 = match p0.parent_code() {
//             Some(c) => {
//                 assert_eq!(c.internal, 0b1_11);
//                 c
//             }
//             None => panic!("Expected parent but code was not found"),
//         };
//         if p1.parent_code().is_some() {
//             panic!("Expected code to be a root code");
//         }
//     }
//
//     #[test]
//     fn test_child_code() {
//         let root = LocationalCode2D::new_root(Child::TopLeft);
//         assert_eq!(
//             root.child_code(Child::BottomLeft).unwrap().internal,
//             0b1_10_00
//         );
//         assert_eq!(
//             root.child_code(Child::BottomRight).unwrap().internal,
//             0b1_10_01
//         );
//         assert_eq!(
//             root.child_code(Child::TopLeft).unwrap().internal,
//             0b1_10_10
//         );
//         assert_eq!(
//             root.child_code(Child::TopRight).unwrap().internal,
//             0b1_10_11
//         );
//     }
//
//     #[test]
//     fn test_neighbour_code() {
//         // Bottom left root node
//         let node = LocationalCode2D::new_root(Child::BottomLeft);
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(LocationalCode2D::new_root(Child::TopLeft))
//         );
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(LocationalCode2D::new_root(Child::BottomRight))
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//         // Bottom right root node
//         let node = LocationalCode2D::new_root(Child::BottomRight);
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(LocationalCode2D::new_root(Child::TopRight))
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(LocationalCode2D::new_root(Child::BottomLeft))
//         );
//
//         // Top left root node
//         let node = LocationalCode2D::new_root(Child::TopLeft);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(LocationalCode2D::new_root(Child::TopRight))
//         );
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(LocationalCode2D::new_root(Child::BottomLeft))
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//         // Top right root node
//         let node = LocationalCode2D::new_root(Child::TopRight);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(LocationalCode2D::new_root(Child::BottomRight))
//         );
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(LocationalCode2D::new_root(Child::TopLeft))
//         );
//
//         // Test some node at depth 1
//         let node = LocationalCode2D::new_from_code_and_depth(0b00_11, 1).unwrap();
//         let north = LocationalCode2D::new_from_code_and_depth(0b10_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(north)
//         );
//         let east = LocationalCode2D::new_from_code_and_depth(0b01_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(east)
//         );
//         let south = LocationalCode2D::new_from_code_and_depth(0b00_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(south)
//         );
//         let west = LocationalCode2D::new_from_code_and_depth(0b00_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(west)
//         );
//
//         let node = LocationalCode2D::new_from_code_and_depth(0b11_00, 1).unwrap();
//         let north = LocationalCode2D::new_from_code_and_depth(0b11_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(north)
//         );
//         let east = LocationalCode2D::new_from_code_and_depth(0b11_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(east)
//         );
//         let south = LocationalCode2D::new_from_code_and_depth(0b01_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(south)
//         );
//         let west = LocationalCode2D::new_from_code_and_depth(0b10_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(west)
//         );
//
//         // Test corners
//         let node = LocationalCode2D::new_from_code_and_depth(0b00_00, 1).unwrap();
//         let north = LocationalCode2D::new_from_code_and_depth(0b00_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(north)
//         );
//         let east = LocationalCode2D::new_from_code_and_depth(0b00_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(east)
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//         let node = LocationalCode2D::new_from_code_and_depth(0b01_01, 1).unwrap();
//         let north = LocationalCode2D::new_from_code_and_depth(0b01_11, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::North),
//             Some(north)
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::South), None);
//         let west = LocationalCode2D::new_from_code_and_depth(0b01_00, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(west)
//         );
//
//         let node = LocationalCode2D::new_from_code_and_depth(0b10_10, 1).unwrap();
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//         let east = LocationalCode2D::new_from_code_and_depth(0b10_11, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::East),
//             Some(east)
//         );
//         let south = LocationalCode2D::new_from_code_and_depth(0b10_00, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(south)
//         );
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::West), None);
//
//         let node = LocationalCode2D::new_from_code_and_depth(0b11_11, 1).unwrap();
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::North), None);
//         assert_eq!(node.same_depth_neighbour(NeighbourDirection::East), None);
//         let south = LocationalCode2D::new_from_code_and_depth(0b11_01, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::South),
//             Some(south)
//         );
//         let west = LocationalCode2D::new_from_code_and_depth(0b11_10, 1).unwrap();
//         assert_eq!(
//             node.same_depth_neighbour(NeighbourDirection::West),
//             Some(west)
//         );
//     }
// }
