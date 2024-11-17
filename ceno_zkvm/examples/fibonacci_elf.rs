use ceno_emul::{
    ByteAddr, CENO_PLATFORM, EmuContext, InsnKind::EANY, Platform, StepRecord, Tracer, VMState,
    WORD_SIZE, WordAddr,
};
use ceno_zkvm::{
    instructions::riscv::{AddressPadder, DummyExtraConfig, MmuConfig, Rv32imConfig},
    scheme::{
        PublicValues, constants::MAX_NUM_VARIABLES, mock_prover::MockProver, prover::ZKVMProver,
        verifier::ZKVMVerifier,
    },
    state::GlobalState,
    structs::{ZKVMConstraintSystem, ZKVMFixedTraces, ZKVMWitnesses},
    tables::{MemFinalRecord, MemInitRecord, ProgramTableCircuit, initial_registers},
};
use clap::Parser;
use ff_ext::ff::Field;
use goldilocks::GoldilocksExt2;
use itertools::{Itertools, MinMaxResult, chain};
use mpcs::{Basefold, BasefoldRSParams, PolynomialCommitmentScheme};
use std::{
    collections::{HashMap, HashSet},
    panic,
    time::Instant,
};
use tracing_flame::FlameLayer;
use tracing_subscriber::{EnvFilter, Registry, fmt, layer::SubscriberExt};
use transcript::Transcript;

/// Prove the execution of a fixed RISC-V program.
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The maximum number of steps to execute the program.
    #[arg(short, long)]
    max_steps: Option<usize>,
}

fn main() {
    let args = Args::parse();

    type E = GoldilocksExt2;
    type Pcs = Basefold<GoldilocksExt2, BasefoldRSParams>;
    const PROGRAM_SIZE: usize = 1 << 14;
    type ExampleProgramTableCircuit<E> = ProgramTableCircuit<E, PROGRAM_SIZE>;

    // set up logger
    let (flame_layer, _guard) = FlameLayer::with_file("./tracing.folded").unwrap();
    let subscriber = Registry::default()
        .with(
            fmt::layer()
                .compact()
                .with_thread_ids(false)
                .with_thread_names(false),
        )
        .with(EnvFilter::from_default_env())
        .with(flame_layer.with_threads_collapsed(true));
    tracing::subscriber::set_global_default(subscriber).unwrap();

    let sp1_platform = Platform {
        rom_start: 0x0020_0800,
        rom_end: 0x003f_ffff,
        ram_start: 0x0020_0000,
        ram_end: 0xffff_ffff,
        unsafe_ecall_nop: true,
    };
    const STACK_TOP: u32 = 0x0020_0400;
    const STACK_SIZE: u32 = 256;
    let mut address_padder = AddressPadder::new(sp1_platform.ram_start()..=sp1_platform.ram_end());

    let elf_bytes = include_bytes!(r"fibonacci.elf");
    let mut vm = VMState::new_from_elf(sp1_platform, elf_bytes).unwrap();

    // keygen
    let pcs_param = Pcs::setup(1 << MAX_NUM_VARIABLES).expect("Basefold PCS setup");
    let (pp, vp) = Pcs::trim(pcs_param, 1 << MAX_NUM_VARIABLES).expect("Basefold trim");
    let mut zkvm_cs = ZKVMConstraintSystem::default();

    let config = Rv32imConfig::<E>::construct_circuits(&mut zkvm_cs);
    let mmu_config = MmuConfig::<E>::construct_circuits(&mut zkvm_cs);
    let dummy_config = DummyExtraConfig::<E>::construct_circuits(&mut zkvm_cs);
    let prog_config = zkvm_cs.register_table_circuit::<ExampleProgramTableCircuit<E>>();
    zkvm_cs.register_global_state::<GlobalState>();

    let mut zkvm_fixed_traces = ZKVMFixedTraces::default();

    zkvm_fixed_traces.register_table_circuit::<ExampleProgramTableCircuit<E>>(
        &zkvm_cs,
        &prog_config,
        vm.program(),
    );

    let mem_init = {
        let program_addrs = vm
            .program()
            .image
            .iter()
            .map(|(addr, value)| MemInitRecord {
                addr: *addr,
                value: *value,
            });

        let stack_addrs = (1..=STACK_SIZE)
            .map(|i| STACK_TOP - i * WORD_SIZE as u32)
            .map(|addr| MemInitRecord { addr, value: 0 });

        let mem_init = chain!(program_addrs, stack_addrs).collect_vec();
        address_padder.pad_records(mem_init, MmuConfig::<E>::static_mem_size())
    };

    // IO is not used in this program, but it must have a particular size at the moment.
    let io_init = address_padder.pad_records(vec![], MmuConfig::<E>::public_io_size());

    let reg_init = initial_registers();
    config.generate_fixed_traces(&zkvm_cs, &mut zkvm_fixed_traces);
    mmu_config.generate_fixed_traces(
        &zkvm_cs,
        &mut zkvm_fixed_traces,
        &reg_init,
        &mem_init,
        &io_init.iter().map(|rec| rec.addr).collect_vec(),
    );
    dummy_config.generate_fixed_traces(&zkvm_cs, &mut zkvm_fixed_traces);

    let pk = zkvm_cs
        .clone()
        .key_gen::<Pcs>(pp.clone(), vp.clone(), zkvm_fixed_traces.clone())
        .expect("keygen failed");
    let vk = pk.get_vk();

    // proving
    let prover = ZKVMProver::new(pk);
    let verifier = ZKVMVerifier::new(vk);

    let all_records = vm
        .iter_until_halt()
        .take(args.max_steps.unwrap_or(usize::MAX))
        .collect::<Result<Vec<StepRecord>, _>>()
        .expect("vm exec failed");

    for step in all_records.iter().take(20) {
        tracing::trace!("{:?} - {:?}\n", step.insn().codes().kind, step);
    }

    // Find the exit code from the HALT step, if halting at all.
    let exit_code = all_records
        .iter()
        .rev()
        .find(|record| {
            record.insn().codes().kind == EANY
                && record.rs1().unwrap().value == CENO_PLATFORM.ecall_halt()
        })
        .and_then(|halt_record| halt_record.rs2())
        .map(|rs2| rs2.value);

    let final_access = vm.tracer().final_accesses();
    let end_cycle: u32 = vm.tracer().cycle().try_into().unwrap();

    let pi = PublicValues::new(
        exit_code.unwrap_or(0),
        vm.program().entry,
        Tracer::SUBCYCLES_PER_INSN as u32,
        vm.get_pc().into(),
        end_cycle,
        io_init.iter().map(|rec| rec.value).collect_vec(),
    );

    let mut zkvm_witness = ZKVMWitnesses::default();
    // assign opcode circuits
    let dummy_records = config
        .assign_opcode_circuit(&zkvm_cs, &mut zkvm_witness, all_records)
        .unwrap();
    dummy_config
        .assign_opcode_circuit(&zkvm_cs, &mut zkvm_witness, dummy_records)
        .unwrap();
    zkvm_witness.finalize_lk_multiplicities();

    // Find the final register values and cycles.
    let reg_final = reg_init
        .iter()
        .map(|rec| {
            let index = rec.addr as usize;
            if index < VMState::REG_COUNT {
                let vma: WordAddr = CENO_PLATFORM.register_vma(index).into();
                MemFinalRecord {
                    addr: rec.addr,
                    value: vm.peek_register(index),
                    cycle: *final_access.get(&vma).unwrap_or(&0),
                }
            } else {
                // The table is padded beyond the number of registers.
                MemFinalRecord {
                    addr: rec.addr,
                    value: 0,
                    cycle: 0,
                }
            }
        })
        .collect_vec();

    // Find the final memory values and cycles.
    let mem_final = mem_init
        .iter()
        .map(|rec| {
            let vma: WordAddr = rec.addr.into();
            MemFinalRecord {
                addr: rec.addr,
                value: vm.peek_memory(vma),
                cycle: *final_access.get(&vma).unwrap_or(&0),
            }
        })
        .collect_vec();
    debug_memory_ranges(&vm, &mem_final);

    // Find the final public IO cycles.
    let io_final = io_init
        .iter()
        .map(|rec| *final_access.get(&rec.addr.into()).unwrap_or(&0))
        .collect_vec();

    // assign table circuits
    config
        .assign_table_circuit(&zkvm_cs, &mut zkvm_witness)
        .unwrap();
    mmu_config
        .assign_table_circuit(
            &zkvm_cs,
            &mut zkvm_witness,
            &reg_final,
            &mem_final,
            &io_final,
        )
        .unwrap();
    // assign program circuit
    zkvm_witness
        .assign_table_circuit::<ExampleProgramTableCircuit<E>>(&zkvm_cs, &prog_config, vm.program())
        .unwrap();

    MockProver::assert_satisfied_full(zkvm_cs, zkvm_fixed_traces, &zkvm_witness, &pi);
    let timer = Instant::now();

    let transcript = Transcript::new(b"riscv");
    let mut zkvm_proof = prover
        .create_proof(zkvm_witness, pi, transcript)
        .expect("create_proof failed");

    println!(
        "riscv_opcodes::create_proof, time = {}",
        timer.elapsed().as_secs_f64()
    );

    let transcript = Transcript::new(b"riscv");
    assert!(
        verifier
            .verify_proof_halt(zkvm_proof.clone(), transcript, exit_code.is_some())
            .expect("verify proof return with error"),
    );
    match exit_code {
        Some(0) => tracing::info!("exit code 0. Success."),
        Some(code) => tracing::error!("exit code {}. Failure.", code),
        None => tracing::error!("Unfinished execution. max_steps={:?}.", args.max_steps),
    }

    let transcript = Transcript::new(b"riscv");
    // change public input maliciously should cause verifier to reject proof
    zkvm_proof.raw_pi[0] = vec![<GoldilocksExt2 as ff_ext::ExtensionField>::BaseField::ONE];
    zkvm_proof.raw_pi[1] = vec![<GoldilocksExt2 as ff_ext::ExtensionField>::BaseField::ONE];

    // capture panic message, if have
    let default_hook = panic::take_hook();
    panic::set_hook(Box::new(|_info| {
        // by default it will print msg to stdout/stderr
        // we override it to avoid print msg since we will capture the msg by our own
    }));
    let result = panic::catch_unwind(|| verifier.verify_proof(zkvm_proof, transcript));
    panic::set_hook(default_hook);
    match result {
        Ok(res) => {
            res.expect_err("verify proof should return with error");
        }
        Err(err) => {
            let msg: String = if let Some(message) = err.downcast_ref::<&str>() {
                message.to_string()
            } else if let Some(message) = err.downcast_ref::<String>() {
                message.to_string()
            } else if let Some(message) = err.downcast_ref::<&String>() {
                message.to_string()
            } else {
                unreachable!()
            };

            if !msg.starts_with("0th round's prover message is not consistent with the claim") {
                println!("unknown panic {msg:?}");
                panic::resume_unwind(err);
            };
        }
    };
}

fn debug_memory_ranges(vm: &VMState, mem_final: &[MemFinalRecord]) {
    let accessed_addrs = vm
        .tracer()
        .final_accesses()
        .iter()
        .filter(|(_, &cycle)| (cycle != 0))
        .map(|(&addr, _)| addr.baddr())
        .filter(|addr| vm.platform().can_read(addr.0))
        .collect_vec();

    let handled_addrs = mem_final
        .iter()
        .filter(|rec| rec.cycle != 0)
        .map(|rec| ByteAddr(rec.addr))
        .collect::<HashSet<_>>();

    tracing::debug!(
        "Memory range (accessed): {:?}",
        format_segments(vm.platform(), accessed_addrs.iter().copied())
    );
    tracing::debug!(
        "Memory range (handled):  {:?}",
        format_segments(vm.platform(), handled_addrs.iter().copied())
    );

    for addr in &accessed_addrs {
        assert!(handled_addrs.contains(addr), "unhandled addr: {:?}", addr);
    }
}

fn format_segments(
    platform: &Platform,
    addrs: impl Iterator<Item = ByteAddr>,
) -> HashMap<String, MinMaxResult<ByteAddr>> {
    addrs
        .into_grouping_map_by(|addr| format_segment(platform, addr.0))
        .minmax()
}

fn format_segment(platform: &Platform, addr: u32) -> String {
    format!(
        "{}{}{}",
        if platform.can_read(addr) { "R" } else { "-" },
        if platform.can_write(addr) { "W" } else { "-" },
        if platform.can_execute(addr) { "X" } else { "-" },
    )
}
