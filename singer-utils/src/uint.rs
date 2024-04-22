use ff::Field;
use gkr::utils::ceil_log2;
use goldilocks::SmallField;
use itertools::Itertools;
use revm_primitives::U256;
use simple_frontend::structs::{CellId, CircuitBuilder};
use std::{marker::PhantomData, process::exit};

use crate::{constants::RANGE_CHIP_BIT_WIDTH, error::UtilError, structs::UInt};

pub mod add_sub;
pub mod cmp;

pub fn u2fvec<F: SmallField, const W: usize, const C: usize>(x: u64) -> [F; W] {
    let mut x = x;
    let mut ret = [F::ZERO; W];
    for i in 0..ret.len() {
        // Cast to u128 to prevent overflow in case C = 64
        ret[i] = F::from(x & ((1u128 << C) - 1) as u64);
        x = ((x as u128) >> C) as u64;
    }
    ret
}

pub fn u256_to_fvec<F: SmallField, const W: usize, const C: usize>(x: U256) -> [F; W] {
    let mut x = x;
    let mut ret = [F::ZERO; W];
    for i in 0..ret.len() {
        // U256 is least significant first. The limbs are u64. C is assumed to be
        // no more than 64.
        ret[i] = F::from(x.as_limbs()[0] & (((1u128 << C) - 1) as u64));
        x >>= C;
    }
    ret
}

pub fn u256_to_vec<const W: usize, const C: usize>(x: U256) -> [u64; W] {
    let mut x = x;
    let mut ret = [0; W];
    for i in 0..ret.len() {
        // U256 is least significant first. The limbs are u64. C is assumed to be
        // no more than 64.
        ret[i] = x.as_limbs()[0] & ((1 << C) - 1);
        x >>= C;
    }
    ret
}

pub fn u2vec<const W: usize, const C: usize>(x: u64) -> [u64; W] {
    let mut x = x;
    let mut ret = [0; W];
    for i in 0..ret.len() {
        ret[i] = x & ((1 << C) - 1);
        x >>= C;
    }
    ret
}

pub fn u2range_limbs<const W: usize>(x: u64) -> [u64; W] {
    u2vec::<W, RANGE_CHIP_BIT_WIDTH>(x)
}

pub fn u2range_field_limbs<F: SmallField, const W: usize>(x: u64) -> [F; W] {
    u2fvec::<F, W, RANGE_CHIP_BIT_WIDTH>(x)
}

pub fn u256_to_range_field_limbs<F: SmallField, const W: usize>(x: U256) -> [F; W] {
    u256_to_fvec::<F, W, RANGE_CHIP_BIT_WIDTH>(x)
}

impl<const M: usize, const C: usize> TryFrom<&[usize]> for UInt<M, C> {
    type Error = UtilError;
    fn try_from(values: &[usize]) -> Result<Self, Self::Error> {
        if values.len() != Self::N_OPRAND_CELLS {
            panic!(
                "expected = {}, got = {}",
                Self::N_OPRAND_CELLS,
                values.len()
            );
        }
        Ok(Self {
            values: values.to_vec(),
        })
    }
}

impl<const M: usize, const C: usize> TryFrom<Vec<usize>> for UInt<M, C> {
    type Error = UtilError;
    fn try_from(values: Vec<usize>) -> Result<Self, Self::Error> {
        let values = values.as_slice().try_into()?;
        Ok(values)
    }
}

impl<const M: usize, const C: usize> UInt<M, C> {
    pub const N_OPRAND_CELLS: usize = (M + C - 1) / C;
    pub const BIT_SIZE: usize = M;
    pub const LIMB_BIT_SIZE: usize = C;

    pub const N_CARRY_CELLS: usize = Self::N_OPRAND_CELLS;
    pub const N_CARRY_NO_OVERFLOW_CELLS: usize = Self::N_OPRAND_CELLS - 1;

    pub const N_RANGE_CHECK_CELLS: usize =
        Self::N_OPRAND_CELLS * ((C + RANGE_CHIP_BIT_WIDTH - 1) / RANGE_CHIP_BIT_WIDTH);
    pub const N_RANGE_CHECK_NO_OVERFLOW_CELLS: usize =
        (Self::N_OPRAND_CELLS - 1) * ((C + RANGE_CHIP_BIT_WIDTH - 1) / RANGE_CHIP_BIT_WIDTH);

    pub fn values(&self) -> &[CellId] {
        &self.values
    }

    /// Split the given unsigned integer into limbs in little endian.
    /// The given integer should have <= C * n effective bits. If it has more bits, then the
    /// extra bits would be ignored.
    pub fn uint_to_limbs(x: u64) -> [u64; Self::N_OPRAND_CELLS] {
        u2vec::<{ Self::N_OPRAND_CELLS }, C>(x)
    }

    /// Split the given unsigned integer into limbs in little endian for range check.
    /// The given integer should have <= range_bits * n effective bits. If it has more bits, then
    /// the extra bits would be ignored.
    pub fn uint_to_range_no_overflow_limbs(x: u64) -> [u64; Self::N_RANGE_CHECK_NO_OVERFLOW_CELLS] {
        u2range_limbs::<{ Self::N_RANGE_CHECK_NO_OVERFLOW_CELLS }>(x)
    }

    /// Split the given unsigned integer into limbs in little endian for range check, then turn
    /// into field elements.
    /// The given integer should have <= range_bits * n effective bits. If it has more bits, then
    /// the extra bits would be ignored.
    pub fn uint_to_range_no_overflow_field_limbs<F: SmallField>(
        x: u64,
    ) -> [F; Self::N_RANGE_CHECK_NO_OVERFLOW_CELLS] {
        u2range_field_limbs::<F, { Self::N_RANGE_CHECK_NO_OVERFLOW_CELLS }>(x)
    }

    /// Split the given unsigned integer into limbs in little endian for range check, then turn
    /// into field elements.
    /// The given integer should have <= range_bits * n effective bits. If it has more bits, then
    /// the extra bits would be ignored.
    pub fn uint_to_range_field_limbs<F: SmallField>(x: u64) -> [F; Self::N_RANGE_CHECK_CELLS] {
        u2range_field_limbs::<F, { Self::N_RANGE_CHECK_CELLS }>(x)
    }

    /// Split the given unsigned 256-bit integer into limbs in little endian for range check, then
    /// turn into field elements.
    /// The given integer should have <= range_bits * n effective bits. If it has more bits, then
    /// the extra bits would be ignored.
    pub fn u256_to_range_field_limbs<F: SmallField>(x: U256) -> [F; Self::N_RANGE_CHECK_CELLS] {
        u256_to_range_field_limbs::<F, { Self::N_RANGE_CHECK_CELLS }>(x)
    }

    /// Split the given unsigned integer into limbs in little endian for range check.
    /// The given integer should have <= range_bits * n effective bits. If it has more bits, then
    /// the extra bits would be ignored.
    pub fn uint_to_range_limbs(x: u64) -> [u64; Self::N_RANGE_CHECK_CELLS] {
        u2range_limbs::<{ Self::N_RANGE_CHECK_CELLS }>(x)
    }

    /// Split the given unsigned integer into limbs in little endian, and put in field elements.
    /// The given integer should have <= C * n effective bits. If it has more bits, then the
    /// extra bits would be ignored.
    pub fn uint_to_field_elems<F: SmallField>(x: u64) -> [F; Self::N_OPRAND_CELLS] {
        u2fvec::<F, { Self::N_OPRAND_CELLS }, C>(x)
    }

    /// Split the given unsigned 256-bit integer into limbs in little endian, and put in
    /// field elements.
    /// The given integer should have <= C * n effective bits. If it has more bits, then the
    /// extra bits would be ignored.
    pub fn u256_to_field_elems<F: SmallField>(x: U256) -> [F; Self::N_OPRAND_CELLS] {
        u256_to_fvec::<F, { Self::N_OPRAND_CELLS }, C>(x)
    }

    /// Split the given unsigned 256-bit integer into limbs in little endian.
    /// The given integer should have <= C * n effective bits. If it has more bits, then the
    /// extra bits would be ignored.
    pub fn u256_to_limbs(x: U256) -> [u64; Self::N_OPRAND_CELLS] {
        u256_to_vec::<{ Self::N_OPRAND_CELLS }, C>(x)
    }

    pub fn from_range_values<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        range_values: &[CellId],
    ) -> Result<Self, UtilError> {
        let mut values = if C <= M {
            convert_decomp(circuit_builder, range_values, RANGE_CHIP_BIT_WIDTH, C, true)
        } else {
            convert_decomp(circuit_builder, range_values, RANGE_CHIP_BIT_WIDTH, M, true)
        };
        while values.len() < Self::N_OPRAND_CELLS {
            values.push(circuit_builder.create_cell());
        }
        Self::try_from(values)
    }

    pub fn from_bytes_big_endien<F: SmallField>(
        circuit_builder: &mut CircuitBuilder<F>,
        bytes: &[CellId],
    ) -> Result<Self, UtilError> {
        let mut values = if C <= M {
            convert_decomp(circuit_builder, bytes, 8, C, true)
        } else {
            convert_decomp(circuit_builder, bytes, 8, M, true)
        };
        while values.len() < Self::N_OPRAND_CELLS {
            values.push(circuit_builder.create_cell());
        }
        Self::try_from(values)
    }

    pub fn assert_eq<F: SmallField>(&self, circuit_builder: &mut CircuitBuilder<F>, other: &Self) {
        for i in 0..self.values.len() {
            let diff = circuit_builder.create_cell();
            circuit_builder.add(diff, self.values[i], F::BaseField::ONE);
            circuit_builder.add(diff, other.values[i], -F::BaseField::ONE);
            circuit_builder.assert_const_debug(diff, 0, "UInt::assert_eq");
        }
    }

    pub fn assert_eq_debug<F: SmallField>(
        &self,
        circuit_builder: &mut CircuitBuilder<F>,
        other: &Self,
        debug_info: &'static str,
    ) {
        for i in 0..self.values.len() {
            let diff = circuit_builder.create_cell();
            circuit_builder.add(diff, self.values[i], F::BaseField::ONE);
            circuit_builder.add(diff, other.values[i], -F::BaseField::ONE);
            circuit_builder.assert_const_debug(diff, 0, debug_info);
        }
    }

    pub fn assert_eq_range_values<F: SmallField>(
        &self,
        circuit_builder: &mut CircuitBuilder<F>,
        range_values: &[CellId],
    ) {
        let values = if C <= M {
            convert_decomp(circuit_builder, range_values, RANGE_CHIP_BIT_WIDTH, C, true)
        } else {
            convert_decomp(circuit_builder, range_values, RANGE_CHIP_BIT_WIDTH, M, true)
        };
        let length = self.values.len().min(values.len());
        for i in 0..length {
            let diff = circuit_builder.create_cell();
            circuit_builder.add(diff, self.values[i], F::BaseField::ONE);
            circuit_builder.add(diff, values[i], -F::BaseField::ONE);
            circuit_builder.assert_const_debug(diff, 0, "UInt::assert_eq_range_values diff");
        }
        for i in length..values.len() {
            circuit_builder.assert_const_debug(values[i], 0, "UInt::assert_eq_range_values values");
        }
        for i in length..self.values.len() {
            circuit_builder.assert_const_debug(
                self.values[i],
                0,
                "UInt::assert_eq_range_values self.values",
            );
        }
    }

    /// Generate (0, 1, ...,  size)
    pub fn counter_vector<F: SmallField>(size: usize) -> Vec<F> {
        let num_vars = ceil_log2(size);
        let tensor = |a: &[F], b: Vec<F>| {
            let mut res = vec![F::ZERO; a.len() * b.len()];
            for i in 0..b.len() {
                for j in 0..a.len() {
                    res[i * a.len() + j] = b[i] * a[j];
                }
            }
            res
        };
        let counter = (0..(1 << C)).map(|x| F::from(x as u64)).collect_vec();
        let (di, mo) = (num_vars / C, num_vars % C);
        let mut res = (0..(1 << mo)).map(|x| F::from(x as u64)).collect_vec();
        for _ in 0..di {
            res = tensor(&counter, res);
        }
        res
    }
}

pub struct UIntAddSub<UInt> {
    _phantom: PhantomData<UInt>,
}
pub struct UIntCmp<UInt> {
    _phantom: PhantomData<UInt>,
}

/// Big-endian bytes to little-endien field values. We don't require
/// `BIG_BIT_WIDTH` % `SMALL_BIT_WIDTH` == 0 because we assume `small_values`
/// can be splitted into chunks with size ceil(BIG_BIT_WIDTH / SMALL_BIT_WIDTH).
/// Each chunk is converted to a value with BIG_BIT_WIDTH bits.
fn convert_decomp<F: SmallField>(
    circuit_builder: &mut CircuitBuilder<F>,
    small_values: &[CellId],
    small_bit_width: usize,
    big_bit_width: usize,
    is_little_endian: bool,
) -> Vec<CellId> {
    let small_values = if is_little_endian {
        small_values.to_vec()
    } else {
        small_values.iter().rev().map(|x: &usize| *x).collect_vec()
    };
    let chunk_size = (big_bit_width + small_bit_width - 1) / small_bit_width;
    let small_len = small_values.len();
    let values = (0..small_len)
        .step_by(chunk_size)
        .map(|j| {
            let tmp = circuit_builder.create_cell();
            for k in j..(j + chunk_size).min(small_len) {
                let k = k as usize;
                circuit_builder.add(
                    tmp,
                    small_values[k],
                    F::BaseField::from((1 as u64) << (k - j) * small_bit_width),
                );
            }
            tmp
        })
        .collect_vec();
    values
}

#[cfg(test)]
mod test {
    use crate::uint::convert_decomp;

    use super::UInt;
    use gkr::structs::{Circuit, CircuitWitness};
    use goldilocks::Goldilocks;
    use simple_frontend::structs::CircuitBuilder;

    #[test]
    fn test_convert_decomp() {
        // test case 1
        let mut circuit_builder = CircuitBuilder::<Goldilocks>::new();
        let big_bit_width = 3;
        let small_bit_width = 2;
        let (small_values_wire_in_id, small_values) = circuit_builder.create_witness_in(31);
        let values = convert_decomp(
            &mut circuit_builder,
            &small_values,
            small_bit_width,
            big_bit_width,
            true,
        );
        assert_eq!(values.len(), 16);
        circuit_builder.configure();
        let circuit = Circuit::new(&circuit_builder);
        let n_witness_in = circuit.n_witness_in;
        let mut wires_in = vec![vec![]; n_witness_in];
        wires_in[small_values_wire_in_id as usize] =
            vec![Goldilocks::from(1u64), Goldilocks::from(1u64)];
        wires_in[small_values_wire_in_id as usize].extend(vec![Goldilocks::from(0u64); 29]);
        let circuit_witness = {
            let challenges = vec![Goldilocks::from(2)];
            let mut circuit_witness = CircuitWitness::new(&circuit, challenges);
            circuit_witness.add_instance(&circuit, wires_in);
            circuit_witness
        };
        #[cfg(feature = "test-dbg")]
        println!("{:?}", circuit_witness);
        circuit_witness.check_correctness(&circuit);
        // check the result
        let result_values = circuit_witness.output_layer_witness_ref();
        assert_eq!(result_values.instances[0][0], Goldilocks::from(5u64));
        for i in 1..16 {
            assert_eq!(result_values.instances[0][i], Goldilocks::from(0u64));
        }
        // test case 2
        let mut circuit_builder = CircuitBuilder::<Goldilocks>::new();
        let big_bit_width = 32;
        let small_bit_width = 16;
        let (small_values_wire_in_id, small_values) = circuit_builder.create_witness_in(4);
        let values = convert_decomp(
            &mut circuit_builder,
            &small_values,
            small_bit_width,
            big_bit_width,
            true,
        );
        assert_eq!(values.len(), 2);
        circuit_builder.configure();
        let circuit = Circuit::new(&circuit_builder);
        let n_witness_in = circuit.n_witness_in;
        let mut wires_in = vec![vec![]; n_witness_in];
        wires_in[small_values_wire_in_id as usize] = vec![
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(1u64),
            Goldilocks::from(0u64),
        ];
        let circuit_witness = {
            let challenges = vec![Goldilocks::from(2)];
            let mut circuit_witness = CircuitWitness::new(&circuit, challenges);
            circuit_witness.add_instance(&circuit, wires_in);
            circuit_witness
        };
        #[cfg(feature = "test-dbg")]
        println!("{:?}", circuit_witness);
        circuit_witness.check_correctness(&circuit);
        // check the result
        let result_values = circuit_witness.output_layer_witness_ref();
        assert_eq!(
            result_values.instances[0],
            vec![Goldilocks::from(0u64), Goldilocks::from(1u64)]
        );
    }

    #[test]
    fn test_from_range_values() {
        let mut circuit_builder = CircuitBuilder::<Goldilocks>::new();
        let (range_values_wire_in_id, range_values) = circuit_builder.create_witness_in(16);
        let range_value =
            UInt::<256, 32>::from_range_values(&mut circuit_builder, &range_values).unwrap();
        assert_eq!(range_value.values.len(), 8);
        circuit_builder.configure();
        let circuit = Circuit::new(&circuit_builder);
        let n_witness_in = circuit.n_witness_in;
        let mut wires_in = vec![vec![]; n_witness_in];
        wires_in[range_values_wire_in_id as usize] = vec![
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(1u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
            Goldilocks::from(0u64),
        ];
        let circuit_witness = {
            let challenges = vec![Goldilocks::from(2)];
            let mut circuit_witness = CircuitWitness::new(&circuit, challenges);
            circuit_witness.add_instance(&circuit, wires_in);
            circuit_witness
        };
        #[cfg(feature = "test-dbg")]
        println!("{:?}", circuit_witness);
        circuit_witness.check_correctness(&circuit);
        // check the result
        let result_values = circuit_witness.output_layer_witness_ref();
        assert_eq!(
            result_values.instances[0],
            vec![
                Goldilocks::from(0),
                Goldilocks::from(1),
                Goldilocks::from(0),
                Goldilocks::from(0),
                Goldilocks::from(0),
                Goldilocks::from(0),
                Goldilocks::from(0),
                Goldilocks::from(0),
            ]
        );
    }
}
