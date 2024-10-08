use ram_circuit::{RamTable, RamTableCircuit};

use crate::structs::RAMType;

mod ram_circuit;
mod ram_impl;

pub struct MemTable;

impl RamTable for MemTable {
    const RAM_TYPE: RAMType = RAMType::Memory;
    const V_LIMBS: usize = 1;
    fn len() -> usize {
        1 << 16
    }

    fn init_state() -> Vec<u32> {
        vec![0; Self::len()]
    }
}
pub type MemTableCircuit<E> = RamTableCircuit<E, MemTable>;

pub struct RIVRegTable;

impl RamTable for RIVRegTable {
    const RAM_TYPE: RAMType = RAMType::Register;
    const V_LIMBS: usize = 1;
    fn len() -> usize {
        32 // register size 32
    }

    fn init_state() -> Vec<u32> {
        // hardcode special initial value for register
        vec![0; Self::len()]
    }
}

pub type RegTableCircuit<E> = RamTableCircuit<E, RIVRegTable>;