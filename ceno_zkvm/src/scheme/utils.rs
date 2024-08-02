use std::{collections::BTreeMap, sync::Arc};

use ff_ext::ExtensionField;
use itertools::Itertools;
use multilinear_extensions::{
    commutative_op_mle_pair,
    mle::{DenseMultilinearExtension, FieldType, IntoMLE},
    op_mle,
    util::ceil_log2,
    virtual_poly_v2::ArcMultilinearExtension,
};
use rayon::{
    iter::{
        IndexedParallelIterator, IntoParallelRefIterator, IntoParallelRefMutIterator,
        ParallelIterator,
    },
    prelude::ParallelSliceMut,
};
use simple_frontend::structs::WitnessId;
use singer_utils::util_v2::Expression;

use crate::scheme::constants::MIN_PAR_SIZE;

/// interleaving multiple mles into mles for the product/logup arguments last layer witness
pub(crate) fn interleaving_mles_to_mles<'a, E: ExtensionField>(
    mles: &[ArcMultilinearExtension<E>],
    log2_num_instances: usize,
    log2_per_instance_size: usize,
    num_product_fanin: usize,
    default: E,
) -> Vec<ArcMultilinearExtension<'a, E>> {
    assert!(num_product_fanin.is_power_of_two());
    let mle_group_len = mles.len() / num_product_fanin;
    let log_num_product_fanin = ceil_log2(num_product_fanin);
    mles.chunks(mle_group_len)
        .map(|records_mle| {
            // interleaving records witness into single vector
            let mut evaluations = vec![
                default;
                1 << (log2_num_instances + log2_per_instance_size
                    - log_num_product_fanin)
            ];
            let per_instance_size = 1 << (log2_per_instance_size - log_num_product_fanin);
            records_mle
                .iter()
                .enumerate()
                .for_each(|(record_i, record_mle)| match record_mle.evaluations() {
                    FieldType::Ext(record_mle) => record_mle
                        .par_iter()
                        .zip(evaluations.par_chunks_mut(per_instance_size))
                        .with_min_len(MIN_PAR_SIZE)
                        .for_each(|(value, instance)| {
                            assert_eq!(instance.len(), per_instance_size);
                            instance[record_i] = *value;
                        }),
                    _ => {
                        unreachable!("must be extension field")
                    }
                });
            evaluations.into_mle().into()
        })
        .collect::<Vec<ArcMultilinearExtension<E>>>()
}

/// infer tower witness from last layer
pub(crate) fn infer_tower_product_witness<'a, E: ExtensionField>(
    num_vars: usize,
    last_layer: Vec<ArcMultilinearExtension<'a, E>>,
    num_product_fanin: usize,
) -> Vec<Vec<ArcMultilinearExtension<'a, E>>> {
    assert!(last_layer.len() == num_product_fanin);
    let mut r_wit_layers = (0..num_vars - 1).fold(vec![last_layer], |mut acc, _| {
        let next_layer = acc.last().unwrap();
        let cur_len = next_layer[0].evaluations().len() / num_product_fanin;
        let cur_layer: Vec<ArcMultilinearExtension<E>> = (0..num_product_fanin)
            .map(|index| {
                let mut evaluations = vec![E::ONE; cur_len];
                next_layer.iter().for_each(|f| match f.evaluations() {
                    FieldType::Ext(f) => {
                        let start: usize = index * cur_len;
                        f[start..][..cur_len]
                            .par_iter()
                            .zip(evaluations.par_iter_mut())
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|(v, evaluations)| *evaluations *= *v)
                            .collect()
                    }
                    _ => unreachable!("must be extension field"),
                });
                evaluations.into_mle().into()
            })
            .collect_vec();
        acc.push(cur_layer);
        acc
    });
    r_wit_layers.reverse();
    r_wit_layers
}

pub(crate) fn wit_infer_by_expr<'a, E: ExtensionField>(
    witnesses: &BTreeMap<WitnessId, DenseMultilinearExtension<E>>,
    challenges: &[E],
    expr: &Expression<E>,
) -> ArcMultilinearExtension<'a, E> {
    expr.evaluate::<ArcMultilinearExtension<'_, E>>(
        &|witness_id| {
            let a: ArcMultilinearExtension<E> = Arc::new(
                witnesses
                    .get(&witness_id)
                    .expect("non exist witness")
                    .clone(),
            );
            a
        },
        &|scalar| {
            let scalar: ArcMultilinearExtension<E> = Arc::new(
                DenseMultilinearExtension::from_evaluations_vec(0, vec![scalar]),
            );
            scalar
        },
        &|challenge_id, pow, scalar, offset| {
            // TODO cache challenge power to be aquire once for each power
            let challenge = challenges[challenge_id as usize];
            let challenge: ArcMultilinearExtension<E> =
                Arc::new(DenseMultilinearExtension::from_evaluations_ext_vec(
                    0,
                    vec![challenge.pow(&[pow as u64]) * scalar + offset],
                ));
            challenge
        },
        &|a, b| {
            commutative_op_mle_pair!(|a, b| {
                match (a.len(), b.len()) {
                    (1, 1) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        0,
                        vec![a[0] + b[0]],
                    )),
                    (1, _) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        ceil_log2(b.len()),
                        b.par_iter()
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|b| a[0] + *b)
                            .collect(),
                    )),
                    (_, 1) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        ceil_log2(a.len()),
                        a.par_iter()
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|a| *a + b[0])
                            .collect(),
                    )),
                    (_, _) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        ceil_log2(a.len()),
                        a.par_iter()
                            .zip(b.par_iter())
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|(a, b)| *a + b)
                            .collect(),
                    )),
                }
            })
        },
        &|a, b| {
            commutative_op_mle_pair!(|a, b| {
                match (a.len(), b.len()) {
                    (1, 1) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        0,
                        vec![a[0] * b[0]],
                    )),
                    (1, _) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        ceil_log2(b.len()),
                        b.par_iter()
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|b| a[0] * *b)
                            .collect(),
                    )),
                    (_, 1) => Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                        ceil_log2(a.len()),
                        a.par_iter()
                            .with_min_len(MIN_PAR_SIZE)
                            .map(|a| *a * b[0])
                            .collect(),
                    )),
                    (_, _) => {
                        unimplemented!("r,w only support degree 1 expression")
                    }
                }
            })
        },
        &|a, scalar| {
            op_mle!(|a| {
                Arc::new(DenseMultilinearExtension::from_evaluation_vec_smart(
                    ceil_log2(a.len()),
                    a.par_iter()
                        .with_min_len(MIN_PAR_SIZE)
                        .map(|a| scalar * a)
                        .collect(),
                ))
            })
        },
    )
}

pub(crate) fn eval_by_expr<'a, E: ExtensionField>(
    witnesses: &[E],
    challenges: &[E],
    expr: &Expression<E>,
) -> E {
    expr.evaluate::<E>(
        &|witness_id| witnesses[witness_id as usize],
        &|scalar| E::from_bases(&[scalar]),
        &|challenge_id, pow, scalar, offset| {
            // TODO cache challenge power to be aquire once for each power
            let challenge = challenges[challenge_id as usize];
            challenge.pow(&[pow as u64]) * scalar + offset
        },
        &|a, b| a + b,
        &|a, b| a * b,
        &|a, scalar| a * scalar,
    )
}

#[cfg(test)]
mod tests {
    use ff::Field;
    use goldilocks::{ExtensionField, GoldilocksExt2};
    use multilinear_extensions::{
        commutative_op_mle_pair,
        mle::{FieldType, IntoMLE},
        util::ceil_log2,
        virtual_poly_v2::ArcMultilinearExtension,
    };

    use crate::scheme::utils::{infer_tower_product_witness, interleaving_mles_to_mles};

    #[test]
    fn test_infer_tower_witness() {
        type E = GoldilocksExt2;
        let num_product_fanin = 2;
        let last_layer: Vec<ArcMultilinearExtension<E>> = vec![
            vec![E::ONE, E::from(2u64)].into_mle().into(),
            vec![E::from(3u64), E::from(4u64)].into_mle().into(),
        ];
        let num_vars = ceil_log2(last_layer[0].evaluations().len()) + 1;
        let res = infer_tower_product_witness(num_vars, last_layer.clone(), 2);
        let (left, right) = (&res[0][0], &res[0][1]);
        let final_product = commutative_op_mle_pair!(
            |left, right| {
                assert!(left.len() == 1 && right.len() == 1);
                left[0] * right[0]
            },
            |out| E::from_base(&out)
        );
        let expected_final_product: E = last_layer
            .iter()
            .map(|f| match f.evaluations() {
                FieldType::Ext(e) => e.iter().cloned().reduce(|a, b| a * b).unwrap(),
                _ => unreachable!(""),
            })
            .product();
        assert_eq!(res.len(), num_vars);
        assert!(
            res.iter()
                .all(|layer_wit| layer_wit.len() == num_product_fanin)
        );
        assert_eq!(final_product, expected_final_product);
    }

    #[test]
    fn test_interleaving_mles_to_mles() {
        type E = GoldilocksExt2;
        let num_product_fanin = 2;
        // [[1, 2], [3, 4]]
        let input_mles: Vec<ArcMultilinearExtension<E>> = vec![
            vec![E::ONE, E::from(2u64)].into_mle().into(),
            vec![E::from(3u64), E::from(4u64)].into_mle().into(),
        ];
        let res = interleaving_mles_to_mles(&input_mles, 1, 2, num_product_fanin, E::ONE);
        // [[1, 1, 2, 1], [3, 1, 4, 1]]
        assert!(res[0].get_ext_field_vec() == vec![E::ONE, E::ONE, E::from(2u64), E::ONE],);
        assert!(res[1].get_ext_field_vec() == vec![E::from(3u64), E::ONE, E::from(4u64), E::ONE]);
    }
}