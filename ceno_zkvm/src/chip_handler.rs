use ff_ext::ExtensionField;

use crate::{
    error::ZKVMError,
    expression::{Expression, WitIn},
    instructions::riscv::config::ExprLtConfig,
};

pub mod general;
pub mod global_state;
pub mod memory;
pub mod register;
pub mod utils;

pub trait GlobalStateRegisterMachineChipOperations<E: ExtensionField> {
    fn state_in(&mut self, pc: Expression<E>, ts: Expression<E>) -> Result<(), ZKVMError>;

    fn state_out(&mut self, pc: Expression<E>, ts: Expression<E>) -> Result<(), ZKVMError>;
}

/// The common representation of a register value.
/// Format: `[u16; 2]`, least-significant-first.
pub type RegisterExpr<E> = [Expression<E>; 2];

pub trait RegisterChipOperations<E: ExtensionField, NR: Into<String>, N: FnOnce() -> NR> {
    fn register_read(
        &mut self,
        name_fn: N,
        register_id: &WitIn,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        value: RegisterExpr<E>,
    ) -> Result<(Expression<E>, ExprLtConfig), ZKVMError>;

    #[allow(clippy::too_many_arguments)]
    fn register_write(
        &mut self,
        name_fn: N,
        register_id: &WitIn,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        prev_values: RegisterExpr<E>,
        value: RegisterExpr<E>,
    ) -> Result<(Expression<E>, ExprLtConfig), ZKVMError>;
}

/// The common representation of a memory value.
/// Format: `[u16; 2]`, least-significant-first.
pub type MemoryExpr<E> = [Expression<E>; 2];

pub trait MemoryChipOperations<E: ExtensionField, NR: Into<String>, N: FnOnce() -> NR> {
    #[allow(dead_code)]
    fn memory_read(
        &mut self,
        name_fn: N,
        memory_addr: &WitIn,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        value: MemoryExpr<E>,
    ) -> Result<(Expression<E>, ExprLtConfig), ZKVMError>;

    #[allow(clippy::too_many_arguments)]
    #[allow(dead_code)]
    fn memory_write(
        &mut self,
        name_fn: N,
        memory_addr: &WitIn,
        prev_ts: Expression<E>,
        ts: Expression<E>,
        prev_values: MemoryExpr<E>,
        value: MemoryExpr<E>,
    ) -> Result<(Expression<E>, ExprLtConfig), ZKVMError>;
}

pub fn register_expr_to_memory_expr<E: ExtensionField>(value: &RegisterExpr<E>) -> MemoryExpr<E> {
    let expression_values = value.to_vec();
    [expression_values[0].clone(), expression_values[1].clone()]
}

pub fn memory_expr_to_register_expr<E: ExtensionField>(value: &MemoryExpr<E>) -> RegisterExpr<E> {
    let expression_values = value.to_vec();
    [expression_values[0].clone(), expression_values[1].clone()]
}
