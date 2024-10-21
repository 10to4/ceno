use crate::{
    chip_handler::{AddressExpr, MemoryChipOperations, MemoryExpr},
    circuit_builder::CircuitBuilder,
    error::ZKVMError,
    expression::Expression,
    gadgets::AssertLTConfig,
    instructions::riscv::constants::UINT_LIMBS,
    structs::RAMType,
};
use ff_ext::ExtensionField;

impl<'a, E: ExtensionField, Name: Into<String>> MemoryChipOperations<E, Name>
    for CircuitBuilder<'a, E>
{
    #[allow(dead_code)]
    fn memory_read(
        &mut self,
        name: Name,
        memory_addr: &AddressExpr<E>,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        value: MemoryExpr<E>,
    ) -> Result<(Expression<E>, AssertLTConfig), ZKVMError> {
        self.namespace(name, |cb| {
            // READ (a, v, t)
            let read_record = cb.rlc_chip_record(
                [
                    vec![
                        Expression::<E>::Constant(E::BaseField::from(RAMType::Memory as u64)),
                        memory_addr.clone(),
                    ],
                    value.to_vec(),
                    vec![prev_ts.clone()],
                ]
                .concat(),
            );
            // Write (a, v, t)
            let write_record = cb.rlc_chip_record(
                [
                    vec![
                        Expression::<E>::Constant(E::BaseField::from(RAMType::Memory as u64)),
                        memory_addr.clone(),
                    ],
                    value.to_vec(),
                    vec![ts.clone()],
                ]
                .concat(),
            );
            cb.read_record("read_record", read_record)?;
            cb.write_record("write_record", write_record)?;

            // assert prev_ts < current_ts
            let lt_cfg = AssertLTConfig::construct_circuit(
                cb,
                "prev_ts < ts",
                prev_ts,
                ts.clone(),
                UINT_LIMBS,
            )?;

            let next_ts = ts + 1.into();

            Ok((next_ts, lt_cfg))
        })
    }

    fn memory_write(
        &mut self,
        name: Name,
        memory_addr: &AddressExpr<E>,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        prev_values: MemoryExpr<E>,
        value: MemoryExpr<E>,
    ) -> Result<(Expression<E>, AssertLTConfig), ZKVMError> {
        self.namespace(name, |cb| {
            // READ (a, v, t)
            let read_record = cb.rlc_chip_record(
                [
                    vec![
                        Expression::<E>::Constant(E::BaseField::from(RAMType::Memory as u64)),
                        memory_addr.clone(),
                    ],
                    prev_values.to_vec(),
                    vec![prev_ts.clone()],
                ]
                .concat(),
            );
            // Write (a, v, t)
            let write_record = cb.rlc_chip_record(
                [
                    vec![
                        Expression::<E>::Constant(E::BaseField::from(RAMType::Memory as u64)),
                        memory_addr.clone(),
                    ],
                    value.to_vec(),
                    vec![ts.clone()],
                ]
                .concat(),
            );
            cb.read_record("read_record", read_record)?;
            cb.write_record("write_record", write_record)?;

            let lt_cfg = AssertLTConfig::construct_circuit(
                cb,
                "prev_ts < ts",
                prev_ts,
                ts.clone(),
                UINT_LIMBS,
            )?;

            let next_ts = ts + 1.into();

            Ok((next_ts, lt_cfg))
        })
    }
}
