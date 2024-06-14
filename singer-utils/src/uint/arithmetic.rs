use crate::chip_handler::RangeChipOperations;
use crate::error::UtilError;
use crate::uint::uint::UInt;
use ff::Field;
use ff_ext::ExtensionField;
use simple_frontend::structs::{Cell, CellId, CircuitBuilder};

impl<const M: usize, const C: usize> UInt<M, C> {
    /// Little-endian addition.
    /// Assumes users will check the correct range of the result themselves.
    // Addition of A + B with limbs [a, b, c] and [d, e, f] respectively
    //
    // cell_modulo = 2^C
    // addend_0 - a                 b                   c
    // addend_1 - d                 e                   f
    //            --------------------------------------------------
    // result   - (a + d) % 2^C    (b + e) % 2^C       (c + f) % 2^C
    // carry    - (a + d) // 2^C   (b + e) // 2^C      (c + f) % 2^C
    //
    // every limb in addend_0 and addend_1 exists in the range [0, ..., 2^C - 1]
    // after summing two limb values, the result exists in [0, ..., 2^(C+1) - 2]
    // the carry value is either 0 or 1,
    // it cannot be >= 2 as that will require result value >= 2^(C+1)
    //
    // assuming result range check, there is a unique carry vector that makes all
    // constraint pass.
    // if a + b > max_cell_value then carry must be set to 1 (if not range check fails)
    // if a + b <= max_cell_value then carry must be set to 0 (if not range check fails)
    //
    // NOTE: this function doesn't perform the required range check!
    pub fn add_unsafe<E: ExtensionField>(
        circuit_builder: &mut CircuitBuilder<E>,
        addend_0: &UInt<M, C>,
        addend_1: &UInt<M, C>,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(Self::N_OPERAND_CELLS)
            .try_into()?;

        for i in 0..Self::N_OPERAND_CELLS {
            let (a, b, result) = (addend_0.values[i], addend_1.values[i], result.values[i]);

            // result = a + b - overflow_carry + last_carry
            circuit_builder.add(result, a, E::BaseField::ONE);
            circuit_builder.add(result, b, E::BaseField::ONE);
            Self::handle_carry(result, circuit_builder, i, carry);
        }

        Ok(result)
    }

    /// Little-endian addition.
    pub fn add<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        addend_0: &UInt<M, C>,
        addend_1: &UInt<M, C>,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Add a constant value to a `UInt<M, C>` instance
    /// Assumes users will check the correct range of the result themselves.
    pub fn add_const_unsafe<E: ExtensionField>(
        circuit_builder: &mut CircuitBuilder<E>,
        addend_0: &UInt<M, C>,
        constant: E::BaseField,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(Self::N_OPERAND_CELLS)
            .try_into()?;

        // add constant to the first limb
        circuit_builder.add_const(result.values[0], constant);

        // cascade carry
        for i in 0..Self::N_OPERAND_CELLS {
            let (a, result) = (addend_0.values[i], result.values[i]);

            circuit_builder.add(result, a, E::BaseField::ONE);
            Self::handle_carry(result, circuit_builder, i, carry);
        }

        Ok(result)
    }

    /// Add a constant value to every cell in the `UInt<M, C>` instance
    pub fn add_const<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        addend_0: &UInt<M, C>,
        constant: E::BaseField,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_const_unsafe(circuit_builder, addend_0, constant, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Add a constant value to every cell in the `UInt<M, C>` instance
    /// Assumes that addition leads to no overflow.
    pub fn add_const_no_overflow<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        addend_0: &UInt<M, C>,
        constant: E::BaseField,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let carry = Self::extract_carry_no_overflow(witness);
        let range_values = Self::extract_range_values_no_overflow(witness);
        let computed_result = Self::add_const_unsafe(circuit_builder, addend_0, constant, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Adds a single cell value to every operand in the `UInt<M, C>` instance
    /// Assumes users will check the correct range of the result and
    /// guarantee addend_1 < 1 << C.
    pub fn add_small_unsafe<E: ExtensionField>(
        circuit_builder: &mut CircuitBuilder<E>,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        carry: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(Self::N_OPERAND_CELLS)
            .try_into()?;

        // add small_value to the first limb
        circuit_builder.add(result.values[0], addend_1, E::BaseField::ONE);

        // cascade carry
        for i in 0..Self::N_OPERAND_CELLS {
            let (a, result) = (addend_0.values[i], result.values[i]);

            circuit_builder.add(result, a, E::BaseField::ONE);
            Self::handle_carry(result, circuit_builder, i, carry);
        }

        Ok(result)
    }

    /// Adds a single cell value to every operand in the `UInt<M, C>` instance
    /// Assumes users will guarantee addend_1 < 1 << C.
    pub fn add_small<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let carry = Self::extract_carry(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::add_small_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Adds a single cell value to every operand in the `UInt<M, C>` instance
    /// Assumes users will guarantee addend_1 < 1 << C.
    /// Assumes that addition lead to no overflow.
    pub fn add_small_no_overflow<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        addend_0: &UInt<M, C>,
        addend_1: CellId,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let carry = Self::extract_carry_no_overflow(witness);
        let range_values = Self::extract_range_values_no_overflow(witness);
        let computed_result = Self::add_small_unsafe(circuit_builder, addend_0, addend_1, carry)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Little endian subtraction
    /// Assumes users will check the correct range of the result themselves.
    pub fn sub_unsafe<E: ExtensionField>(
        circuit_builder: &mut CircuitBuilder<E>,
        minuend: &UInt<M, C>,
        subtrahend: &UInt<M, C>,
        borrow: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let result: UInt<M, C> = circuit_builder
            .create_cells(Self::N_OPERAND_CELLS)
            .try_into()?;

        for i in 0..Self::N_OPERAND_CELLS {
            let (minuend, subtrahend, result) =
                (minuend.values[i], subtrahend.values[i], result.values[i]);

            circuit_builder.add(result, minuend, E::BaseField::ONE);
            circuit_builder.add(result, subtrahend, -E::BaseField::ONE);

            if i < borrow.len() {
                circuit_builder.add(result, borrow[i], E::BaseField::from(1 << C));
            }

            if i > 0 && i - 1 < borrow.len() {
                circuit_builder.add(result, borrow[i - 1], -E::BaseField::ONE);
            }
        }

        Ok(result)
    }

    /// Little endian subtraction
    pub fn sub<E: ExtensionField, H: RangeChipOperations<E>>(
        circuit_builder: &mut CircuitBuilder<E>,
        range_chip_handler: &mut H,
        minuend: &UInt<M, C>,
        subtrahend: &UInt<M, C>,
        witness: &[CellId],
    ) -> Result<UInt<M, C>, UtilError> {
        let borrow = Self::extract_borrow(witness);
        let range_values = Self::extract_range_values(witness);
        let computed_result = Self::sub_unsafe(circuit_builder, minuend, subtrahend, borrow)?;
        range_chip_handler.range_check_uint(circuit_builder, &computed_result, Some(range_values))
    }

    /// Modify addition result based on carry instructions
    fn handle_carry<E: ExtensionField>(
        result_cell_id: CellId,
        circuit_builder: &mut CircuitBuilder<E>,
        limb_index: usize,
        carry: &[CellId],
    ) {
        // overflow carry
        // represents the portion of the result that should move to the next operation
        // inorder to keep the value <= C bits
        // carry[i] = addend_0[i] + addend_1[i] % 2^C

        // last carry
        // represents the carry that was passed from the previous operation
        // this carry should be added to the current result
        // carry[i - 1] = addend_0[i - 1] + addend_1[i - 1] % 2^C

        if limb_index > carry.len() {
            return;
        }

        // handle overflow carry
        // we need to subtract the carry value from the current result
        if limb_index < carry.len() {
            circuit_builder.add(
                result_cell_id,
                carry[limb_index],
                -E::BaseField::from(1 << C),
            );
        }

        // handle last operation carry
        // we need to add this to the current result
        if limb_index > 0 {
            circuit_builder.add(result_cell_id, carry[limb_index - 1], E::BaseField::ONE);
        }
    }
}