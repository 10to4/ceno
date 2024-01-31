use std::cmp::min;

use frontend::structs::{CellId, CircuitBuilder, ConstantType};
use goldilocks::SmallField;
use revm_primitives::U256;

use crate::{
    error::ZKVMError,
    instructions::utils::{ChipHandler, UInt},
};

use super::{u2vec, UIntAddSub};

impl<const M: usize, const C: usize> UIntAddSub<UInt<M, C>> {
    pub(in crate::instructions) const N_NO_OVERFLOW_WITNESS_CELLS: usize =
        UInt::<M, C>::N_RANGE_CHECK_CELLS + UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS;
    pub(in crate::instructions) const N_NO_OVERFLOW_WITNESS_UNSAFE_CELLS: usize =
        UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS;

    pub(in crate::instructions) const N_WITNESS_UNSAFE_CELLS: usize = UInt::<M, C>::N_CARRY_CELLS;
    pub(in crate::instructions) const N_WITNESS_CELLS: usize =
        UInt::<M, C>::N_RANGE_CHECK_CELLS + UInt::<M, C>::N_CARRY_CELLS;

    pub(in crate::instructions) fn extract_range_values(witness: &[CellId]) -> &[CellId] {
        &witness[..UInt::<M, C>::N_RANGE_CHECK_CELLS]
    }

    pub(in crate::instructions) fn range_values_range(offset: usize) -> std::ops::Range<usize> {
        offset..offset + UInt::<M, C>::N_RANGE_CHECK_CELLS
    }

    pub(in crate::instructions) fn extract_range_values_no_overflow(
        witness: &[CellId],
    ) -> &[CellId] {
        &witness[..UInt::<M, C>::N_RANGE_CHECK_NO_OVERFLOW_CELLS]
    }

    pub(in crate::instructions) fn range_values_no_overflow_range(
        offset: usize,
    ) -> std::ops::Range<usize> {
        offset..offset + UInt::<M, C>::N_RANGE_CHECK_NO_OVERFLOW_CELLS
    }

    pub(in crate::instructions) fn extract_carry_no_overflow(witness: &[CellId]) -> &[CellId] {
        &witness[UInt::<M, C>::N_RANGE_CHECK_NO_OVERFLOW_CELLS..]
    }

    pub(in crate::instructions) fn carry_no_overflow_range(
        offset: usize,
    ) -> std::ops::Range<usize> {
        offset + UInt::<M, C>::N_RANGE_CHECK_NO_OVERFLOW_CELLS
            ..offset
                + UInt::<M, C>::N_RANGE_CHECK_NO_OVERFLOW_CELLS
                + UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS
    }

    pub(in crate::instructions) fn extract_carry(witness: &[CellId]) -> &[CellId] {
        &witness[UInt::<M, C>::N_RANGE_CHECK_CELLS..]
    }

    pub(in crate::instructions) fn carry_range(offset: usize) -> std::ops::Range<usize> {
        offset + UInt::<M, C>::N_RANGE_CHECK_CELLS
            ..offset + UInt::<M, C>::N_RANGE_CHECK_CELLS + UInt::<M, C>::N_CARRY_CELLS
    }

    pub(in crate::instructions) fn extract_unsafe_carry(witness: &[CellId]) -> &[CellId] {
        witness
    }

    pub(in crate::instructions) fn unsafe_range(offset: usize) -> std::ops::Range<usize> {
        offset..offset + UInt::<M, C>::N_CARRY_CELLS
    }

    pub(in crate::instructions) fn compute_no_overflow_carries<F: SmallField>(
        addend_0: u64,
        addend_1: u64,
    ) -> [F; UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut carry = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS];
        for (i, (a, b)) in UInt::<M, C>::uint_to_limbs(addend_0)
            .iter()
            .zip(UInt::<M, C>::uint_to_limbs(addend_1).iter())
            .enumerate()
        {
            carry = a + b + if carry { 1 } else { 0 } >= (1 << C);
            if i < ret.len() {
                ret[i] = if carry { F::ONE } else { F::ZERO };
            }
        }
        ret
    }

    pub(in crate::instructions) fn compute_carries<F: SmallField>(
        addend_0: u64,
        addend_1: u64,
    ) -> [F; UInt::<M, C>::N_CARRY_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut carry = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_CELLS];
        for (i, (a, b)) in UInt::<M, C>::uint_to_limbs(addend_0)
            .iter()
            .zip(UInt::<M, C>::uint_to_limbs(addend_1).iter())
            .enumerate()
        {
            carry = a + b + if carry { 1 } else { 0 } >= (1 << C);
            if i < ret.len() {
                ret[i] = if carry { F::ONE } else { F::ZERO };
            }
        }
        ret
    }

    pub(in crate::instructions) fn compute_carries_u256<F: SmallField>(
        addend_0: U256,
        addend_1: U256,
    ) -> [F; UInt::<M, C>::N_CARRY_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut carry = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_CELLS];
        for (i, (a, b)) in UInt::<M, C>::u256_to_limbs(addend_0)
            .iter()
            .zip(UInt::<M, C>::u256_to_limbs(addend_1).iter())
            .enumerate()
        {
            carry = a + b + if carry { 1 } else { 0 } >= (1 << C);
            if i < ret.len() {
                ret[i] = if carry { F::ONE } else { F::ZERO };
            }
        }
        ret
    }

    pub(in crate::instructions) fn compute_no_overflow_borrows<F: SmallField>(
        minuend: u64,
        subtrahend: u64,
    ) -> [F; UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut borrow = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_NO_OVERFLOW_CELLS];
        for (i, (a, b)) in UInt::<M, C>::uint_to_limbs(minuend)
            .iter()
            .zip(UInt::<M, C>::uint_to_limbs(subtrahend).iter())
            .enumerate()
        {
            // If a - borrow (from previous limb) < b, then should borrow in this limb
            borrow = b + if borrow { 1 } else { 0 } > *a;
            // The highest borrow is omitted since we assume it's not overflowing
            if i < ret.len() {
                ret[i] = if borrow { F::ONE } else { F::ZERO };
            }
        }
        ret
    }

    pub(in crate::instructions) fn compute_borrows<F: SmallField>(
        minuend: u64,
        subtrahend: u64,
    ) -> [F; UInt::<M, C>::N_CARRY_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut borrow = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_CELLS];
        for (i, (a, b)) in UInt::<M, C>::uint_to_limbs(minuend)
            .iter()
            .zip(UInt::<M, C>::uint_to_limbs(subtrahend).iter())
            .enumerate()
        {
            // If a - borrow (from previous limb) < b, then should borrow in this limb
            borrow = b + if borrow { 1 } else { 0 } > *a;
            ret[i] = if borrow { F::ONE } else { F::ZERO };
        }
        ret
    }

    pub(in crate::instructions) fn compute_borrows_u256<F: SmallField>(
        minuend: U256,
        subtrahend: U256,
    ) -> [F; UInt::<M, C>::N_CARRY_CELLS]
    // This weird where clause is a hack because of the issue
    // https://github.com/rust-lang/rust/issues/82509
    where
        [(); UInt::<M, C>::N_OPRAND_CELLS]:,
    {
        let mut borrow = false;
        let mut ret = [F::ZERO; UInt::<M, C>::N_CARRY_CELLS];
        for (i, (a, b)) in UInt::<M, C>::u256_to_limbs(minuend)
            .iter()
            .zip(UInt::<M, C>::u256_to_limbs(subtrahend).iter())
            .enumerate()
        {
            // If a - borrow (from previous limb) < b, then should borrow in this limb
            borrow = b + if borrow { 1 } else { 0 } > *a;
            ret[i] = if borrow { F::ONE } else { F::ZERO };
        }
        ret
    }

    /// Little-endian addition. Assume users to check the correct range of the
    /// result by themselves.
    pub(in crate::instructions) fn add_unsafe<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        addend_0: &UInt<M, C>,
        addend_1: &UInt<M, C>,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(UInt::<M, C>::N_OPRAND_CELLS)
            .try_into()?;
        for i in 0..UInt::<M, C>::N_OPRAND_CELLS {
            let (a, b, result) = (addend_0.values[i], addend_1.values[i], result.values[i]);
            // result = addend_0 + addend_1 + last_carry - carry * (1 << VALUE_BIT_WIDTH)
            circuit_builder.add(result, a, ConstantType::Field(F::ONE));
            circuit_builder.add(result, b, ConstantType::Field(F::ONE));
            // It is equivalent to pad carry with 0s.
            if i < carry.len() {
                circuit_builder.add(result, carry[i], ConstantType::Field(-F::from(1 << C)));
            }
            if i > 0 && i - 1 < carry.len() {
                circuit_builder.add(result, carry[i - 1], ConstantType::Field(F::ONE));
            }
        }
        Ok(result)
    }

    /// Little-endian addition.
    pub(in crate::instructions) fn add<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_chip_handler: &mut ChipHandler,
        addend_0: &UInt<M, C>,
        addend_1: &UInt<M, C>,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little-endian addition with a constant. Assume users to check the
    /// correct range of the result by themselves.
    pub(in crate::instructions) fn add_const_unsafe<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        addend_0: &UInt<M, C>,
        constant: &F,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(UInt::<M, C>::N_OPRAND_CELLS)
            .try_into()?;
        for i in 0..result.values.len() {
            let (a, result) = (addend_0.values[i], result.values[i]);
            // result = addend_0 + addend_1 + last_carry - carry * (256 << BYTE_WIDTH)
            circuit_builder.add(result, a, ConstantType::Field(F::ONE));
            circuit_builder.add_const(result, ConstantType::Field(*constant));
            // It is equivalent to pad carry with 0s.
            if i < carry.len() {
                circuit_builder.add(result, carry[i], ConstantType::Field(-F::from(1 << C)));
            }
            if i > 0 && i - 1 < carry.len() {
                circuit_builder.add(result, carry[i - 1], ConstantType::Field(F::ONE));
            }
        }
        Ok(result)
    }

    /// Little-endian addition with a constant.
    pub(in crate::instructions) fn add_const<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_chip_handler: &mut ChipHandler,
        addend_0: &UInt<M, C>,
        constant: &F,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_const_unsafe(circuit_builder, addend_0, constant, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little-endian addition with a constant, guaranteed no overflow.
    pub(in crate::instructions) fn add_const_no_overflow<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_chip_handler: &mut ChipHandler,
        addend_0: &UInt<M, C>,
        constant: &F,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let carry = Self::extract_carry_no_overflow(witness);
        let range_values = Self::extract_range_values_no_overflow(witness);
        let computed_result = Self::add_const_unsafe(circuit_builder, addend_0, constant, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little-endian addition with a small number. Notice that the user should
    /// guarantee addend_1 < 1 << C.
    pub(in crate::instructions) fn add_small_unsafe<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(UInt::<M, C>::N_OPRAND_CELLS)
            .try_into()?;
        for i in 0..result.values.len() {
            let (a, result) = (addend_0.values[i], result.values[i]);
            // result = addend_0 + addend_1 + last_carry - carry * (256 << BYTE_WIDTH)
            circuit_builder.add(result, a, ConstantType::Field(F::ONE));
            circuit_builder.add(result, addend_1, ConstantType::Field(F::ONE));
            // It is equivalent to pad carry with 0s.
            if i < carry.len() {
                circuit_builder.add(result, carry[i], ConstantType::Field(-F::from(1 << C)));
            }
            if i > 0 && i - 1 < carry.len() {
                circuit_builder.add(result, carry[i - 1], ConstantType::Field(F::ONE));
            }
        }
        Ok(result)
    }

    /// Little-endian addition with a small number. Notice that the user should
    /// guarantee addend_1 < 1 << C.
    pub(in crate::instructions) fn add_small<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_chip_handler: &mut ChipHandler,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_small_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little-endian addition with a small number, guaranteed no overflow.
    /// Notice that the user should guarantee addend_1 < 1 << C.
    pub(in crate::instructions) fn add_small_no_overflow<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_chip_handler: &mut ChipHandler,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let carry = Self::extract_carry_no_overflow(witness);
        let range_values = Self::extract_range_values_no_overflow(witness);
        let computed_result = Self::add_small_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little-endian subtraction. Assume users to check the correct range of
    /// the result by themselves.
    pub(in crate::instructions) fn sub_unsafe<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        minuend: &UInt<M, C>,
        subtrahend: &UInt<M, C>,
        borrow: &[CellId],
    ) -> Result<UInt<M, C>, ZKVMError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(UInt::<M, C>::N_OPRAND_CELLS)
            .try_into()?;
        // result = minuend - subtrahend + borrow * (1 << BIT_WIDTH) - last_borrow
        for i in 0..result.values.len() {
            let (minuend, subtrahend, result) =
                (minuend.values[i], subtrahend.values[i], result.values[i]);
            circuit_builder.add(result, minuend, ConstantType::Field(F::ONE));
            circuit_builder.add(result, subtrahend, ConstantType::Field(-F::ONE));
            // When borrow does not provide the highest bit, the highest borrow bit is treated
            // as zero.
            if i < borrow.len() {
                circuit_builder.add(result, borrow[i], ConstantType::Field(F::from(1 << C)));
            }
            if i > 0 && i - 1 < borrow.len() {
                circuit_builder.add(result, borrow[i - 1], ConstantType::Field(-F::ONE));
            }
        }
        Ok(result)
    }
}