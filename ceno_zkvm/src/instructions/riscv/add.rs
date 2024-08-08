use std::marker::PhantomData;

use ff_ext::ExtensionField;

use singer_utils::{self, constants::OpcodeType};

use crate::{
    chip_handler::{GlobalStateRegisterMachineChipOperations, RegisterChipOperations},
    circuit_builder::CircuitBuilder,
    error::ZKVMError,
    expression::{ToExpr, WitIn},
    instructions::Instruction,
    structs::{PCUInt, TSUInt, UInt64},
};

use super::constants::RISCV64_PC_STEP_SIZE;

pub struct AddInstruction;

pub struct InstructionConfig<E: ExtensionField> {
    pub pc: PCUInt,
    pub ts: TSUInt,
    pub prev_rd_memory_value: UInt64,
    pub addend_0: UInt64,
    pub addend_1: UInt64,
    pub outcome: UInt64,
    pub rs1_id: WitIn,
    pub rs2_id: WitIn,
    pub rd_id: WitIn,
    pub prev_rs1_ts: TSUInt,
    pub prev_rs2_ts: TSUInt,
    pub prev_rd_ts: TSUInt,
    phantom: PhantomData<E>,
}

impl<E: ExtensionField> Instruction<E> for AddInstruction {
    const OPCODE: OpcodeType = OpcodeType::ADD;
    const NAME: &'static str = "ADD";
    type InstructionConfig = InstructionConfig<E>;
    fn construct_circuit(
        circuit_builder: &mut CircuitBuilder<E>,
    ) -> Result<InstructionConfig<E>, ZKVMError> {
        let pc = PCUInt::new(circuit_builder);
        let mut ts = TSUInt::new(circuit_builder);

        // state in
        circuit_builder.state_in(&pc, &ts)?;

        let next_pc = pc.add_const(circuit_builder, RISCV64_PC_STEP_SIZE.into())?;

        // Execution result = addend0 + addend1, with carry.
        let prev_rd_memory_value = UInt64::new(circuit_builder);
        let addend_0 = UInt64::new(circuit_builder);
        let addend_1 = UInt64::new(circuit_builder);
        let outcome = UInt64::new(circuit_builder);

        let computed_outcome = addend_0.add(circuit_builder, &addend_1)?;
        outcome.eq(circuit_builder, &computed_outcome)?;

        // TODO rs1_id, rs2_id, rd_id should be bytecode lookup
        let rs1_id = circuit_builder.create_witin();
        let rs2_id = circuit_builder.create_witin();
        let rd_id = circuit_builder.create_witin();
        circuit_builder.assert_u5(rs1_id.expr())?;
        circuit_builder.assert_u5(rs2_id.expr())?;
        circuit_builder.assert_u5(rd_id.expr())?;

        let mut prev_rs1_ts = TSUInt::new(circuit_builder);
        let mut prev_rs2_ts = TSUInt::new(circuit_builder);
        let mut prev_rd_ts = TSUInt::new(circuit_builder);

        let mut ts =
            circuit_builder.register_read(&rs1_id, &mut prev_rs1_ts, &mut ts, &addend_0)?;

        let mut ts =
            circuit_builder.register_read(&rs2_id, &mut prev_rs2_ts, &mut ts, &addend_1)?;

        let ts = circuit_builder.register_write(
            &rd_id,
            &mut prev_rd_ts,
            &mut ts,
            &prev_rd_memory_value,
            &computed_outcome,
        )?;

        let next_ts = ts.add_const(circuit_builder, 1.into())?;
        circuit_builder.state_out(&next_pc, &next_ts)?;

        Ok(InstructionConfig {
            pc,
            ts,
            prev_rd_memory_value,
            addend_0,
            addend_1,
            outcome,
            rs1_id,
            rs2_id,
            rd_id,
            prev_rs1_ts,
            prev_rs2_ts,
            prev_rd_ts,
            phantom: PhantomData,
        })
    }
}

#[cfg(test)]
mod test {
    use std::collections::BTreeMap;

    use ark_std::test_rng;
    use ff::Field;
    use ff_ext::ExtensionField;
    use gkr::structs::PointAndEval;
    use goldilocks::{Goldilocks, GoldilocksExt2};
    use multilinear_extensions::mle::IntoMLE;
    use simple_frontend::structs::WitnessId;
    use transcript::Transcript;

    use crate::{
        circuit_builder::CircuitBuilder,
        instructions::Instruction,
        scheme::{constants::NUM_FANIN, prover::ZKVMProver, verifier::ZKVMVerifier},
    };

    use super::AddInstruction;

    #[test]
    fn test_add_construct_circuit() {
        let mut rng = test_rng();

        let mut circuit_builder = CircuitBuilder::<GoldilocksExt2>::new();
        let _ = AddInstruction::construct_circuit(&mut circuit_builder);
        let circuit = circuit_builder.finalize_circuit();

        // generate mock witness
        let mut wits_in = BTreeMap::new();
        let num_instances = 1 << 2;
        (0..circuit.num_witin as usize).for_each(|witness_id| {
            wits_in.insert(
                witness_id as WitnessId,
                (0..num_instances)
                    .map(|_| Goldilocks::random(&mut rng))
                    .collect::<Vec<Goldilocks>>()
                    .into_mle(),
            );
        });

        // get proof
        let prover = ZKVMProver::new(circuit.clone()); // circuit clone due to verifier alos need circuit reference
        let mut transcript = Transcript::new(b"riscv");
        let challenges = vec![1.into(), 2.into()];

        let mut proof = prover
            .create_proof(wits_in, num_instances, 1, &mut transcript, &challenges)
            .expect("create_proof failed");

        let verifier = ZKVMVerifier::new(circuit);
        let mut v_transcript = Transcript::new(b"riscv");
        let _rt_input = verifier
            .verify(
                &mut proof,
                &mut v_transcript,
                NUM_FANIN,
                &PointAndEval::default(),
                &challenges,
            )
            .expect("verifier failed");
        // TODO verify opening via PCS
    }

    fn bench_add_instruction_helper<E: ExtensionField>(_instance_num_vars: usize) {}

    #[test]
    fn bench_add_instruction() {
        bench_add_instruction_helper::<GoldilocksExt2>(10);
    }
}