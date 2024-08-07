use std::collections::BTreeMap;

use ff_ext::ExtensionField;
use gkr::{entered_span, exit_span, structs::Point};

use itertools::Itertools;
use multilinear_extensions::{
    mle::{DenseMultilinearExtension, IntoMLE, MultilinearExtension},
    util::ceil_log2,
    virtual_poly::build_eq_x_r_vec,
    virtual_poly_v2::ArcMultilinearExtension,
};
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use simple_frontend::structs::WitnessId;
use sumcheck::structs::{IOPProverMessage, IOPProverStateV2};
use transcript::Transcript;

use crate::{
    circuit_builder::Circuit,
    error::ZKVMError,
    scheme::{
        constants::{MAINCONSTRAIN_SUMCHECK_BATCH_SIZE, NUM_FANIN},
        utils::{
            infer_tower_logup_witness, infer_tower_product_witness, interleaving_mles_to_mles,
            wit_infer_by_expr,
        },
    },
    structs::{TowerProofs, TowerProver, TowerProverSpec, VirtualPolynomials},
    utils::{get_challenge_pows, proper_num_threads},
};

use super::ZKVMProof;

pub struct ZKVMProver<E: ExtensionField> {
    circuit: Circuit<E>,
}

impl<E: ExtensionField> ZKVMProver<E> {
    pub fn new(circuit: Circuit<E>) -> Self {
        ZKVMProver { circuit }
    }

    /// create proof giving witness and num_instances
    /// major flow break down into
    /// 1: witness layer inferring from input -> output
    /// 2: proof (sumcheck reduce) from output to input
    pub fn create_proof(
        &self,
        witnesses: BTreeMap<WitnessId, DenseMultilinearExtension<E>>,
        num_instances: usize,
        max_threads: usize,
        transcript: &mut Transcript<E>,
        challenges: &[E],
    ) -> Result<ZKVMProof<E>, ZKVMError> {
        let circuit = &self.circuit;
        let log2_num_instances = ceil_log2(num_instances);
        let next_pow2_instances = 1 << log2_num_instances;

        // sanity check
        assert_eq!(witnesses.len(), circuit.num_witin as usize);
        witnesses.iter().all(|(_, v)| {
            v.num_vars() == log2_num_instances && v.evaluations().len() == next_pow2_instances
        });

        // main constraint: read/write record witness inference
        let span = entered_span!("wit_inference::record");
        let records_wit: Vec<ArcMultilinearExtension<'_, E>> = circuit
            .r_expressions
            .par_iter()
            .chain(circuit.w_expressions.par_iter())
            .chain(circuit.lk_expressions.par_iter())
            .map(|expr| {
                assert_eq!(expr.degree(), 1);
                wit_infer_by_expr(&witnesses, &challenges, expr)
            })
            .collect();
        let (r_records_wit, w_lk_records_wit) = records_wit.split_at(circuit.r_expressions.len());
        let (w_records_wit, lk_records_wit) =
            w_lk_records_wit.split_at(circuit.w_expressions.len());
        exit_span!(span);

        // product constraint: tower witness inference
        let (r_counts_per_instance, w_counts_per_instance, lk_counts_per_instance) = (
            circuit.r_expressions.len(),
            circuit.w_expressions.len(),
            circuit.lk_expressions.len(),
        );
        let (log2_r_count, log2_w_count, log2_lk_count) = (
            ceil_log2(r_counts_per_instance),
            ceil_log2(w_counts_per_instance),
            ceil_log2(lk_counts_per_instance),
        );
        // process last layer by interleaving all the read/write record respectively
        // as last layer is the output of sel stage
        let span = entered_span!("wit_inference::tower_witness_r_last_layer");
        // TODO optimize last layer to avoid alloc new vector to save memory
        let r_records_last_layer = interleaving_mles_to_mles(
            r_records_wit,
            log2_num_instances,
            log2_r_count,
            NUM_FANIN,
            E::ONE,
        );
        assert_eq!(r_records_last_layer.len(), NUM_FANIN);
        exit_span!(span);

        // infer all tower witness after last layer
        let span = entered_span!("wit_inference::tower_witness_r_layers");
        let r_wit_layers = infer_tower_product_witness(
            log2_num_instances + log2_r_count,
            r_records_last_layer,
            NUM_FANIN,
        );
        exit_span!(span);

        let span = entered_span!("wit_inference::tower_witness_w_last_layer");
        // TODO optimize last layer to avoid alloc new vector to save memory
        let w_records_last_layer = interleaving_mles_to_mles(
            w_records_wit,
            log2_num_instances,
            log2_w_count,
            NUM_FANIN,
            E::ONE,
        );
        assert_eq!(w_records_last_layer.len(), NUM_FANIN);
        exit_span!(span);

        let span = entered_span!("wit_inference::tower_witness_w_layers");
        let w_wit_layers = infer_tower_product_witness(
            log2_num_instances + log2_w_count,
            w_records_last_layer,
            NUM_FANIN,
        );
        exit_span!(span);

        let span = entered_span!("wit_inference::tower_witness_lk_last_layer");
        // TODO optimize last layer to avoid alloc new vector to save memory
        let lk_records_last_layer = interleaving_mles_to_mles(
            lk_records_wit,
            log2_num_instances,
            log2_lk_count,
            2,
            E::ZERO,
        );
        assert_eq!(lk_records_last_layer.len(), 2);
        exit_span!(span);

        let span = entered_span!("wit_inference::tower_witness_lk_layers");
        let lk_wit_layers = infer_tower_logup_witness(lk_records_last_layer.try_into().unwrap());
        exit_span!(span);

        if cfg!(test) {
            // sanity check
            assert_eq!(lk_wit_layers.len(), (log2_num_instances + log2_lk_count));
            assert_eq!(r_wit_layers.len(), (log2_num_instances + log2_r_count));
            assert_eq!(w_wit_layers.len(), (log2_num_instances + log2_w_count));
            assert!(lk_wit_layers.iter().enumerate().all(|(i, w)| {
                let expected_size = 1 << i;
                let (p1, p2, q1, q2) = (&w[0], &w[1], &w[2], &w[3]);
                p1.evaluations().len() == expected_size
                    && p2.evaluations().len() == expected_size
                    && q1.evaluations().len() == expected_size
                    && q2.evaluations().len() == expected_size
            }));
            assert!(r_wit_layers.iter().enumerate().all(|(i, r_wit_layer)| {
                let expected_size = 1 << (ceil_log2(NUM_FANIN) * i);
                r_wit_layer.len() == NUM_FANIN
                    && r_wit_layer
                        .iter()
                        .all(|f| f.evaluations().len() == expected_size)
            }));
            assert!(w_wit_layers.iter().enumerate().all(|(i, w_wit_layer)| {
                let expected_size = 1 << (ceil_log2(NUM_FANIN) * i);
                w_wit_layer.len() == NUM_FANIN
                    && w_wit_layer
                        .iter()
                        .all(|f| f.evaluations().len() == expected_size)
            }));
        }

        // product constraint tower sumcheck
        let span = entered_span!("sumcheck::tower");
        // final evals for verifier
        let record_r_out_evals: Vec<E> = r_wit_layers[0]
            .iter()
            .map(|w| w.get_ext_field_vec()[0])
            .collect();
        let record_w_out_evals: Vec<E> = w_wit_layers[0]
            .iter()
            .map(|w| w.get_ext_field_vec()[0])
            .collect();
        let lk_p1_out_eval = lk_wit_layers[0][0].get_ext_field_vec()[0];
        let lk_p2_out_eval = lk_wit_layers[0][1].get_ext_field_vec()[0];
        let lk_q1_out_eval = lk_wit_layers[0][2].get_ext_field_vec()[0];
        let lk_q2_out_eval = lk_wit_layers[0][3].get_ext_field_vec()[0];
        assert!(record_r_out_evals.len() == NUM_FANIN && record_w_out_evals.len() == NUM_FANIN);
        let (rt_tower, tower_proof) = TowerProver::create_proof(
            max_threads,
            vec![
                TowerProverSpec {
                    witness: r_wit_layers,
                },
                TowerProverSpec {
                    witness: w_wit_layers,
                },
            ],
            vec![TowerProverSpec {
                witness: lk_wit_layers,
            }],
            NUM_FANIN,
            transcript,
        );
        assert_eq!(
            rt_tower.len(),
            log2_num_instances
                + vec![log2_r_count, log2_w_count, log2_lk_count]
                    .iter()
                    .max()
                    .unwrap()
        );
        exit_span!(span);

        // batch sumcheck: selector + main degree > 1 constraints
        let span = entered_span!("sumcheck::main_sel");
        let (rt_r, rt_w, rt_lk): (Vec<E>, Vec<E>, Vec<E>) = (
            rt_tower[..log2_num_instances + log2_r_count].to_vec(),
            rt_tower[..log2_num_instances + log2_w_count].to_vec(),
            rt_tower[..log2_num_instances + log2_lk_count].to_vec(),
        );

        let num_threads = proper_num_threads(log2_num_instances, max_threads);
        let alpha_pow = get_challenge_pows(MAINCONSTRAIN_SUMCHECK_BATCH_SIZE, transcript);
        let (alpha_read, alpha_write, alpha_lk) = (&alpha_pow[0], &alpha_pow[1], &alpha_pow[2]);
        // create selector: all ONE, but padding ZERO to ceil_log2
        let (sel_r, sel_w, sel_lk): (
            ArcMultilinearExtension<E>,
            ArcMultilinearExtension<E>,
            ArcMultilinearExtension<E>,
        ) = {
            // TODO sel can be shared if expression count match
            let mut sel_r = build_eq_x_r_vec(&rt_r[log2_r_count..]);
            if num_instances < sel_r.len() {
                sel_r.splice(num_instances..sel_r.len(), std::iter::repeat(E::ZERO));
            }

            let mut sel_w = build_eq_x_r_vec(&rt_w[log2_w_count..]);
            if num_instances < sel_w.len() {
                sel_w.splice(num_instances..sel_w.len(), std::iter::repeat(E::ZERO));
            }

            let mut sel_lk = build_eq_x_r_vec(&rt_lk[log2_lk_count..]);
            if num_instances < sel_lk.len() {
                sel_lk.splice(num_instances..sel_lk.len(), std::iter::repeat(E::ZERO));
            }

            (
                sel_r.into_mle().into(),
                sel_w.into_mle().into(),
                sel_lk.into_mle().into(),
            )
        };
        let mut virtual_polys = VirtualPolynomials::<E>::new(num_threads, log2_num_instances);
        let sel_r_threads = virtual_polys.get_all_range_polys(&sel_r);
        let sel_w_threads: Vec<ArcMultilinearExtension<'_, E>> =
            virtual_polys.get_all_range_polys(&sel_w);
        let sel_lk_threads: Vec<ArcMultilinearExtension<'_, E>> =
            virtual_polys.get_all_range_polys(&sel_lk);

        let eq_r = build_eq_x_r_vec(&rt_r[..log2_r_count]);
        let eq_w = build_eq_x_r_vec(&rt_w[..log2_w_count]);
        let eq_lk = build_eq_x_r_vec(&rt_lk[..log2_lk_count]);

        // read
        // rt_r := rt || rs
        for (thread_id, sel_r) in (0..num_threads).zip(sel_r_threads.iter()) {
            for i in 0..r_counts_per_instance {
                // \sum_t (sel(rt, t) * (\sum_i alpha_read * eq(rs, i) * record_r[t] ))
                let r_records_wit = virtual_polys
                    .get_range_polys_by_thread_id(thread_id, vec![&r_records_wit[i]])
                    .remove(0);
                virtual_polys.add_mle_list(
                    thread_id,
                    vec![sel_r.clone(), r_records_wit],
                    eq_r[i] * alpha_read,
                );
            }
            // \sum_t alpha_read * sel(rt, t) * (\sum_i (eq(rs, i)) - 1)
            virtual_polys.add_mle_list(
                thread_id,
                vec![sel_r.clone()],
                *alpha_read * eq_r[r_counts_per_instance..].iter().sum::<E>() - *alpha_read,
            );
        }

        // write
        // rt := rt || rs
        for (thread_id, sel_w) in (0..num_threads).zip(sel_w_threads.iter()) {
            for i in 0..w_counts_per_instance {
                // \sum_t (sel(rt, t) * (\sum_i alpha_write * eq(rs, i) * record_w[i] ))
                let w_records_wit = virtual_polys
                    .get_range_polys_by_thread_id(thread_id, vec![&w_records_wit[i]])
                    .remove(0);
                virtual_polys.add_mle_list(
                    thread_id,
                    vec![sel_w.clone(), w_records_wit],
                    eq_w[i] * alpha_write,
                );
            }
            // \sum_t alpha_write * sel(rt, t) * (\sum_i (eq(rs, i)) - 1)
            virtual_polys.add_mle_list(
                thread_id,
                vec![sel_w.clone()],
                *alpha_write * eq_w[w_counts_per_instance..].iter().sum::<E>() - *alpha_write,
            );
        }

        // lk
        // rt := rt || rs
        // padding is 0, therefore we dont need to add padding term
        for (thread_id, sel_lk) in (0..num_threads).zip(sel_lk_threads.iter()) {
            for i in 0..lk_counts_per_instance {
                // \sum_t (sel(rt, t) * (\sum_i alpha_lk* eq(rs, i) * record_w[i] ))
                let lk_records_wit = virtual_polys
                    .get_range_polys_by_thread_id(thread_id, vec![&lk_records_wit[i]])
                    .remove(0);
                virtual_polys.add_mle_list(
                    thread_id,
                    vec![sel_lk.clone(), lk_records_wit.clone()],
                    eq_lk[i] * alpha_lk,
                );
            }
        }
        let (main_sel_sumcheck_proofs, state) = IOPProverStateV2::prove_batch_polys(
            num_threads,
            virtual_polys.get_batched_polys(),
            transcript,
        );
        let main_sel_evals = state.get_mle_final_evaluations();
        assert_eq!(
            main_sel_evals.len(),
            r_counts_per_instance + w_counts_per_instance + lk_counts_per_instance + 3
        ); // 3 from [sel_r, sel_w, sel_lk]
        let mut main_sel_evals_iter = main_sel_evals.into_iter();
        main_sel_evals_iter.next(); // skip sel_r
        let r_records_in_evals = (0..r_counts_per_instance)
            .map(|_| main_sel_evals_iter.next().unwrap())
            .collect_vec();
        main_sel_evals_iter.next(); // skip sel_w
        let w_records_in_evals = (0..w_counts_per_instance)
            .map(|_| main_sel_evals_iter.next().unwrap())
            .collect_vec();
        main_sel_evals_iter.next(); // skip sel_lk
        let lk_records_in_evals = (0..lk_counts_per_instance)
            .map(|_| main_sel_evals_iter.next().unwrap())
            .collect_vec();
        assert!(main_sel_evals_iter.next().is_none());
        let input_open_point = main_sel_sumcheck_proofs.point.clone();
        assert!(input_open_point.len() == log2_num_instances);
        exit_span!(span);

        let span = entered_span!("witin::evals");
        let wits_in_evals = witnesses
            .par_iter()
            .map(|(_, poly)| poly.evaluate(&input_open_point))
            .collect();
        exit_span!(span);

        Ok(ZKVMProof {
            num_instances,
            record_r_out_evals,
            record_w_out_evals,
            lk_p1_out_eval,
            lk_p2_out_eval,
            lk_q1_out_eval,
            lk_q2_out_eval,
            tower_proof,
            main_sel_sumcheck_proofs: main_sel_sumcheck_proofs.proofs,
            r_records_in_evals,
            w_records_in_evals,
            lk_records_in_evals,
            wits_in_evals,
        })
    }
}

/// TowerProofs
impl<E: ExtensionField> TowerProofs<E> {
    pub fn new(prod_spec_size: usize, logup_spec_size: usize) -> Self {
        TowerProofs {
            proofs: vec![],
            prod_specs_eval: vec![vec![]; prod_spec_size],
            logup_specs_eval: vec![vec![]; logup_spec_size],
        }
    }
    pub fn push_sumcheck_proofs(&mut self, proofs: Vec<IOPProverMessage<E>>) {
        self.proofs.push(proofs);
    }

    pub fn push_prod_evals(&mut self, spec_index: usize, evals: Vec<E>) {
        self.prod_specs_eval[spec_index].push(evals);
    }

    pub fn push_logup_evals(&mut self, spec_index: usize, evals: Vec<E>) {
        self.logup_specs_eval[spec_index].push(evals);
    }

    pub fn prod_spec_size(&self) -> usize {
        return self.prod_specs_eval.len();
    }

    pub fn logup_spec_size(&self) -> usize {
        return self.logup_specs_eval.len();
    }
}

/// Tower Prover
impl TowerProver {
    pub fn create_proof<'a, E: ExtensionField>(
        max_threads: usize,
        prod_specs: Vec<TowerProverSpec<'a, E>>,
        logup_specs: Vec<TowerProverSpec<'a, E>>,
        num_fanin: usize,
        transcript: &mut Transcript<E>,
    ) -> (Point<E>, TowerProofs<E>) {
        // XXX to sumcheck batched product argument with logup, we limit num_product_fanin to 2
        // TODO mayber give a better naming?
        assert_eq!(num_fanin, 2);

        let mut proofs = TowerProofs::new(prod_specs.len(), logup_specs.len());
        assert!(prod_specs.len() > 0);
        let log_num_fanin = ceil_log2(num_fanin);
        // -1 for sliding windows size 2: (cur_layer, next_layer) w.r.t total size
        let max_round = prod_specs
            .iter()
            .chain(logup_specs.iter())
            .map(|m| m.witness.len())
            .max()
            .unwrap()
            - 1;

        // generate shared alpha challenge
        // TODO soundness question: should we generate new alpha for each layer?
        let alpha_pows = get_challenge_pows(
            prod_specs.len() +
            // logup occupy 2 sumcheck: numerator and denominator
            logup_specs.len() * 2,
            transcript,
        );
        let initial_rt: Point<E> = (0..log_num_fanin)
            .map(|_| transcript.get_and_append_challenge(b"product_sum").elements)
            .collect_vec();

        let next_rt = (0..max_round).fold(initial_rt, |out_rt, round| {
            // in first few round we just run on single thread
            let num_threads = proper_num_threads(out_rt.len(), max_threads);

            let eq: ArcMultilinearExtension<E> = build_eq_x_r_vec(&out_rt).into_mle().into();
            let mut virtual_polys = VirtualPolynomials::<E>::new(num_threads, out_rt.len());
            // eq_threads is ranged polynomials defined on eq with different range
            let eq_threads: Vec<ArcMultilinearExtension<'_, E>> =
                virtual_polys.get_all_range_polys(&eq);

            for (s, alpha) in prod_specs.iter().zip(alpha_pows.iter()) {
                if (round + 1) < s.witness.len() {
                    let layer_polys = &s.witness[round + 1];

                    // sanity check
                    assert_eq!(layer_polys.len(), num_fanin);
                    layer_polys
                        .iter()
                        .all(|f| f.evaluations().len() == 1 << (log_num_fanin * round));

                    // \sum_s eq(rt, s) * alpha^{i} * ([in_i0[s] * in_i1[s] * .... in_i{num_product_fanin}[s]])
                    for (thread_id, eq) in (0..num_threads).zip(eq_threads.iter()) {
                        let layer_polys = virtual_polys.get_range_polys_by_thread_id(
                            thread_id,
                            layer_polys.iter().map(|x| x).collect(),
                        );
                        virtual_polys.add_mle_list(
                            thread_id,
                            vec![vec![eq.clone()], layer_polys].concat(),
                            *alpha,
                        )
                    }
                }
            }

            for (s, alpha) in logup_specs
                .iter()
                .zip(alpha_pows[prod_specs.len()..].chunks(2))
            {
                if (round + 1) < s.witness.len() {
                    let layer_polys = &s.witness[round + 1];
                    // sanity check
                    assert_eq!(layer_polys.len(), 4); // p1, q1, p2, q2
                    layer_polys
                        .iter()
                        .all(|f| f.evaluations().len() == 1 << (log_num_fanin * round));

                    let (alpha_numerator, alpha_denominator) = (&alpha[0], &alpha[1]);

                    for (thread_id, eq) in (0..num_threads).zip(eq_threads.iter()) {
                        let mut layer_polys = virtual_polys.get_range_polys_by_thread_id(
                            thread_id,
                            layer_polys.iter().map(|x| x).collect(),
                        );
                        let (q2, q1, p2, p1) = (
                            layer_polys.pop().unwrap(),
                            layer_polys.pop().unwrap(),
                            layer_polys.pop().unwrap(),
                            layer_polys.pop().unwrap(),
                        );

                        // \sum_s eq(rt, s) * alpha_numerator^{i} * (p1 * q2 + p2 * q1)
                        virtual_polys.add_mle_list(
                            thread_id,
                            vec![eq.clone(), p1, q2.clone()],
                            *alpha_numerator,
                        );
                        virtual_polys.add_mle_list(
                            thread_id,
                            vec![eq.clone(), p2, q1.clone()],
                            *alpha_numerator,
                        );

                        // \sum_s eq(rt, s) * alpha_denominator^{i} * (q1 * q2)
                        virtual_polys.add_mle_list(
                            thread_id,
                            vec![eq.clone(), q1, q2],
                            *alpha_denominator,
                        );
                    }
                }
            }

            let (sumcheck_proofs, state) = IOPProverStateV2::prove_batch_polys(
                num_threads,
                virtual_polys.get_batched_polys(),
                transcript,
            );
            proofs.push_sumcheck_proofs(sumcheck_proofs.proofs);

            // rt' = r_merge || rt
            let r_merge = (0..log_num_fanin)
                .map(|_| transcript.get_and_append_challenge(b"merge").elements)
                .collect_vec();
            let rt_prime = vec![sumcheck_proofs.point, r_merge].concat();

            let evals = state.get_mle_final_evaluations();
            let mut evals_iter = evals.iter();
            evals_iter.next(); // skip first eq
            for (i, s) in prod_specs.iter().enumerate() {
                if (round + 1) < s.witness.len() {
                    // collect evals belong to current spec
                    proofs.push_prod_evals(
                        i,
                        (0..num_fanin)
                            .map(|_| *evals_iter.next().expect("insufficient evals length"))
                            .collect::<Vec<E>>(),
                    );
                }
            }
            for (i, s) in logup_specs.iter().enumerate() {
                if (round + 1) < s.witness.len() {
                    // collect evals belong to current spec
                    // p1, q2, p2, q1
                    let p1 = *evals_iter.next().expect("insufficient evals length");
                    let q2 = *evals_iter.next().expect("insufficient evals length");
                    let p2 = *evals_iter.next().expect("insufficient evals length");
                    let q1 = *evals_iter.next().expect("insufficient evals length");
                    proofs.push_logup_evals(i, vec![p1, p2, q1, q2]);
                }
            }
            assert_eq!(evals_iter.next(), None);
            rt_prime
        });

        (next_rt, proofs)
    }
}
