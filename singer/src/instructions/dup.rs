use ff::Field;
use gkr::structs::Circuit;
use goldilocks::SmallField;
use paste::paste;
use simple_frontend::structs::{CircuitBuilder, MixedCell};
use std::sync::Arc;

use crate::{
    constants::OpcodeType,
    error::ZKVMError,
    utils::{
        chip_handler::{
            BytecodeChipOperations, ChipHandler, GlobalStateChipOperations, RangeChipOperations,
            StackChipOperations,
        },
        uint::{PCUInt, StackUInt, TSUInt, UIntAddSub, UIntCmp},
    },
};

use super::{ChipChallenges, InstCircuit, InstCircuitLayout, Instruction, InstructionGraph};

pub struct DupInstruction<const N: usize>;

impl<const N: usize> InstructionGraph for DupInstruction<N> {
    type InstType = Self;
}

register_witness!(
    DupInstruction<N>,
    phase0 {
        pc => PCUInt::N_OPRAND_CELLS,
        stack_ts => TSUInt::N_OPRAND_CELLS,
        memory_ts => TSUInt::N_OPRAND_CELLS,
        stack_top => 1,
        clk => 1,

        pc_add => UIntAddSub::<PCUInt>::N_NO_OVERFLOW_WITNESS_UNSAFE_CELLS,
        stack_ts_add => UIntAddSub::<TSUInt>::N_NO_OVERFLOW_WITNESS_CELLS,

        stack_values => StackUInt::N_OPRAND_CELLS,
        old_stack_ts => TSUInt::N_OPRAND_CELLS,
        old_stack_ts_lt => UIntCmp::<TSUInt>::N_NO_OVERFLOW_WITNESS_CELLS
    }
);

impl<const N: usize> DupInstruction<N> {
    const OPCODE: OpcodeType = match N {
        1 => OpcodeType::DUP1,
        2 => OpcodeType::DUP2,
        _ => unimplemented!(),
    };
}

impl<const N: usize> Instruction for DupInstruction<N> {
    fn construct_circuit<F: SmallField>(
        challenges: ChipChallenges,
    ) -> Result<InstCircuit<F>, ZKVMError> {
        let mut circuit_builder = CircuitBuilder::new();
        let (phase0_wire_id, phase0) = circuit_builder.create_wire_in(Self::phase0_size());
        let mut global_state_in_handler = ChipHandler::new(challenges.global_state());
        let mut global_state_out_handler = ChipHandler::new(challenges.global_state());
        let mut bytecode_chip_handler = ChipHandler::new(challenges.bytecode());
        let mut stack_push_handler = ChipHandler::new(challenges.stack());
        let mut stack_pop_handler = ChipHandler::new(challenges.stack());
        let mut range_chip_handler = ChipHandler::new(challenges.range());

        // State update
        let pc = PCUInt::try_from(&phase0[Self::phase0_pc()])?;
        let stack_ts = TSUInt::try_from(&phase0[Self::phase0_stack_ts()])?;
        let memory_ts = &phase0[Self::phase0_memory_ts()];
        let stack_top = phase0[Self::phase0_stack_top().start];
        let stack_top_expr = MixedCell::Cell(stack_top);
        let clk = phase0[Self::phase0_clk().start];
        let clk_expr = MixedCell::Cell(clk);
        global_state_in_handler.state_in(
            &mut circuit_builder,
            pc.values(),
            stack_ts.values(),
            &memory_ts,
            stack_top,
            clk,
        );

        let next_pc = ChipHandler::add_pc_const(
            &mut circuit_builder,
            &pc,
            1,
            &phase0[Self::phase0_pc_add()],
        )?;
        let next_stack_ts = range_chip_handler.add_ts_with_const(
            &mut circuit_builder,
            &stack_ts,
            1,
            &phase0[Self::phase0_stack_ts_add()],
        )?;

        global_state_out_handler.state_out(
            &mut circuit_builder,
            next_pc.values(),
            next_stack_ts.values(),
            &memory_ts,
            stack_top_expr.add(F::BaseField::from(1)),
            clk_expr.add(F::BaseField::ONE),
        );

        // Check the range of stack_top - N is within [0, 1 << STACK_TOP_BIT_WIDTH).
        range_chip_handler.range_check_stack_top(
            &mut circuit_builder,
            stack_top_expr.sub(F::BaseField::from(N as u64)),
        )?;

        // Pop rlc of stack[top - N] from stack
        let old_stack_ts = (&phase0[Self::phase0_old_stack_ts()]).try_into()?;
        UIntCmp::<TSUInt>::assert_lt(
            &mut circuit_builder,
            &mut range_chip_handler,
            &old_stack_ts,
            &stack_ts,
            &phase0[Self::phase0_old_stack_ts_lt()],
        )?;
        let stack_values = &phase0[Self::phase0_stack_values()];
        stack_pop_handler.stack_pop(
            &mut circuit_builder,
            stack_top_expr.sub(F::BaseField::from(1)),
            old_stack_ts.values(),
            stack_values,
        );

        // Check the range of stack_top within [0, 1 << STACK_TOP_BIT_WIDTH).
        range_chip_handler.range_check_stack_top(&mut circuit_builder, stack_top.into())?;
        // Push stack_values twice to stack
        stack_push_handler.stack_push(
            &mut circuit_builder,
            stack_top_expr.sub(F::BaseField::from(1)),
            stack_ts.values(),
            stack_values,
        );
        stack_push_handler.stack_push(
            &mut circuit_builder,
            stack_top_expr,
            stack_ts.values(),
            stack_values,
        );

        // Bytecode check for (pc, DUP{N})
        bytecode_chip_handler.bytecode_with_pc_opcode(
            &mut circuit_builder,
            pc.values(),
            Self::OPCODE,
        );

        let global_state_in_id = global_state_in_handler
            .finalize_with_const_pad(&mut circuit_builder, F::BaseField::ONE);
        let global_state_out_id = global_state_out_handler
            .finalize_with_const_pad(&mut circuit_builder, F::BaseField::ONE);
        let bytecode_chip_id =
            bytecode_chip_handler.finalize_with_repeated_last(&mut circuit_builder);
        let stack_push_id =
            stack_push_handler.finalize_with_const_pad(&mut circuit_builder, F::BaseField::ONE);
        let stack_pop_id =
            stack_pop_handler.finalize_with_const_pad(&mut circuit_builder, F::BaseField::ONE);
        let range_chip_id = range_chip_handler.finalize_with_repeated_last(&mut circuit_builder);
        circuit_builder.configure();

        let outputs_wire_id = [
            Some(global_state_in_id),
            Some(global_state_out_id),
            Some(bytecode_chip_id),
            Some(stack_pop_id),
            Some(stack_push_id),
            Some(range_chip_id),
            None,
            None,
            None,
        ];

        Ok(InstCircuit {
            circuit: Arc::new(Circuit::new(&circuit_builder)),
            layout: InstCircuitLayout {
                chip_check_wire_id: outputs_wire_id,
                phases_wire_id: vec![phase0_wire_id],
                ..Default::default()
            },
        })
    }
}