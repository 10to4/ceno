#![allow(clippy::manual_memcpy)]
#![allow(clippy::needless_range_loop)]

use std::{
    collections::BTreeMap,
    time::{Duration, Instant},
};

use ark_std::test_rng;
use ceno_zkvm::{instructions::riscv::add::AddInstruction, scheme::prover::ZKVMProver};
use const_env::from_env;
use criterion::*;

use ff_ext::ff::Field;
use goldilocks::{Goldilocks, GoldilocksExt2};
use multilinear_extensions::{mle::DenseMultilinearExtension, util::ceil_log2};
use simple_frontend::structs::WitnessId;
use singer_utils::{structs_v2::CircuitBuilderV2, util_v2::InstructionV2};
use transcript::Transcript;

cfg_if::cfg_if! {
  if #[cfg(feature = "flamegraph")] {
    criterion_group! {
      name = op_add;
      config = Criterion::default().warm_up_time(Duration::from_millis(3000)).with_profiler(pprof::criterion::PProfProfiler::new(100, pprof::criterion::Output::Flamegraph(None)));
      targets = bench_add
    }
  } else {
    criterion_group! {
      name = op_add;
      config = Criterion::default().warm_up_time(Duration::from_millis(3000));
      targets = bench_add
    }
  }
}

criterion_main!(op_add);

const NUM_SAMPLES: usize = 10;
#[from_env]
const RAYON_NUM_THREADS: usize = 8;

pub fn is_power_of_2(x: usize) -> bool {
    (x != 0) && ((x & (x - 1)) == 0)
}

fn bench_add(c: &mut Criterion) {
    let max_thread_id = {
        if !is_power_of_2(RAYON_NUM_THREADS) {
            #[cfg(not(feature = "non_pow2_rayon_thread"))]
            {
                panic!(
                    "add --features non_pow2_rayon_thread to enable unsafe feature which support non pow of 2 rayon thread pool"
                );
            }

            #[cfg(feature = "non_pow2_rayon_thread")]
            {
                use sumcheck::{local_thread_pool::create_local_pool_once, util::ceil_log2};
                let max_thread_id = 1 << ceil_log2(RAYON_NUM_THREADS);
                create_local_pool_once(1 << ceil_log2(RAYON_NUM_THREADS), true);
                max_thread_id
            }
        } else {
            RAYON_NUM_THREADS
        }
    };
    let mut circuit_builder = CircuitBuilderV2::<GoldilocksExt2>::new();
    let _ = AddInstruction::construct_circuit(&mut circuit_builder);
    let circuit = circuit_builder.finalize_circuit();
    let num_witin = circuit.num_witin;

    let prover = ZKVMProver::new(circuit); // circuit clone due to verifier alos need circuit reference
    let mut transcript = Transcript::new(b"riscv");

    for instance_num_vars in 20..22 {
        // expand more input size once runtime is acceptable
        let mut group = c.benchmark_group(format!("add_op_{}", instance_num_vars));
        group.sample_size(NUM_SAMPLES);

        // Benchmark the proving time
        group.bench_function(
            BenchmarkId::new("prove_add", format!("prove_add_log2_{}", instance_num_vars)),
            |b| {
                b.iter_with_setup(
                    || {
                        let mut rng = test_rng();
                        let real_challenges = vec![E::random(&mut rng), E::random(&mut rng)];
                        (rng, real_challenges)
                    },
                    |(mut rng, real_challenges)| {
                        // generate mock witness
                        let mut wits_in = BTreeMap::new();
                        let num_instances = 1 << instance_num_vars;
                        (0..num_witin as usize).for_each(|witness_id| {
                            wits_in.insert(
                                witness_id as WitnessId,
                                DenseMultilinearExtension::from_evaluations_vec(
                                    instance_num_vars,
                                    (0..num_instances)
                                        .map(|_| Goldilocks::random(&mut rng))
                                        .collect(),
                                ),
                            );
                        });
                        let timer = Instant::now();
                        let _ = prover
                            .create_proof(wits_in, num_instances, &mut transcript, &real_challenges)
                            .expect("create_proof failed");
                        println!(
                            "AddInstruction::create_proof, instance_num_vars = {}, time = {}",
                            instance_num_vars,
                            timer.elapsed().as_secs_f64()
                        );
                    },
                );
            },
        );

        group.finish();
    }

    type E = GoldilocksExt2;
}