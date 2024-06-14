use super::uint::UInt;
use crate::constants::RANGE_CHIP_BIT_WIDTH;
use crate::uint::util::const_min;

impl<const M: usize, const C: usize> UInt<M, C> {
    /// Determines the maximum number of bits that should be represented in each cell
    /// independent of the cell capacity `C`.
    /// If M < C i.e. total bit < cell capacity, the maximum_usable_cell_capacity
    /// is actually M.
    /// but if M >= C then maximum_usable_cell_capacity = C
    pub const MAX_CELL_BIT_WIDTH: usize = const_min(M, C);

    /// `N_OPERAND_CELLS` represent the minimum number of cells each of size `C` needed
    /// to hold `M` total bits
    pub const N_OPERAND_CELLS: usize = (M + C - 1) / C;

    /// The number of `RANGE_CHIP_BIT_WIDTH` cells needed to represent one cell of size `C`
    const N_RANGE_CELLS_PER_CELL: usize = (C + RANGE_CHIP_BIT_WIDTH - 1) / RANGE_CHIP_BIT_WIDTH;

    /// The number of `RANGE_CHIP_BIT_WIDTH` cells needed to represent the entire `UInt<M, C>`
    pub const N_RANGE_CELLS: usize = Self::N_OPERAND_CELLS * Self::N_RANGE_CELLS_PER_CELL;

    /// The number of `RANGE_CHIP_BIT_WIDTH` cells needed to represent the carry cells, assuming
    /// no overflow.
    pub const N_RANGE_CELLS_IN_CARRY_NO_OVERFLOW: usize =
        Self::N_CARRY_CELLS_NO_OVERFLOW * Self::N_RANGE_CELLS_PER_CELL;

    /// The size of the witness
    pub const N_WITNESS_CELLS: usize = Self::N_RANGE_CELLS + Self::N_CARRY_CELLS;

    /// The size of the witness assuming carry has no overflow
    /// |Range_values| + |Carry - 1|
    pub const N_WITNESS_CELLS_NO_CARRY_OVERFLOW: usize =
        Self::N_RANGE_CELLS + Self::N_CARRY_CELLS_NO_OVERFLOW;

    // TODO: add documentation
    // TODO: why this?
    pub const N_NO_OVERFLOW_WITNESS_UNSAFE_CELLS: usize = Self::N_CARRY_CELLS_NO_OVERFLOW;

    // Arithmetic Constants

    /// Number of cells required to track carry information for the addition operation.
    /// operand_0 =     a   b  c
    /// operand_1 =     e   f  g
    ///                ----------
    /// result    =     h   i  j
    /// carry     =  k  l   m  -
    /// |Carry| = |Cells|
    pub const N_CARRY_CELLS: usize = Self::N_OPERAND_CELLS;

    /// Number of cells required to track carry information if we assume the addition
    /// operation cannot lead to overflow.
    /// operand_0 =     a   b  c
    /// operand_1 =     e   f  g
    ///                ----------
    /// result    =     h   i  j
    /// carry     =     l   m  -
    /// |Carry| = |Cells - 1|
    const N_CARRY_CELLS_NO_OVERFLOW: usize = Self::N_CARRY_CELLS - 1;
}