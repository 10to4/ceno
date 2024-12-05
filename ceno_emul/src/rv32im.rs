// Based on: https://github.com/risc0/risc0/blob/aeea62f0c8f4223abfba17d4c78cb7e15c513de2/risc0/circuit/rv32im/src/prove/emu/rv32im.rs
//
// Copyright 2024 RISC Zero, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use anyhow::{Result, anyhow};
use num_derive::ToPrimitive;
use strum_macros::{Display, EnumIter};

use super::addr::{ByteAddr, RegIdx, WORD_SIZE, Word, WordAddr};

pub trait EmuContext {
    // Handle environment call
    fn ecall(&mut self) -> Result<bool>;

    // Handle a trap
    fn trap(&self, cause: TrapCause) -> Result<bool>;

    // Callback when instructions end normally
    fn on_normal_end(&mut self, _decoded: &Instruction) {}

    // Get the program counter
    fn get_pc(&self) -> ByteAddr;

    // Set the program counter
    fn set_pc(&mut self, addr: ByteAddr);

    // Load from a register
    fn load_register(&mut self, idx: RegIdx) -> Result<Word>;

    // Store to a register
    fn store_register(&mut self, idx: RegIdx, data: Word) -> Result<()>;

    // Load from memory
    fn load_memory(&mut self, addr: WordAddr) -> Result<Word>;

    // Store to memory
    fn store_memory(&mut self, addr: WordAddr, data: Word) -> Result<()>;

    // Get the value of a register without side-effects.
    fn peek_register(&self, idx: RegIdx) -> Word;

    // Get the value of a memory word without side-effects.
    fn peek_memory(&self, addr: WordAddr) -> Word;

    /// Load from instruction cache
    fn fetch(&mut self, pc: WordAddr) -> Option<Instruction>;

    // Check access for data load
    fn check_data_load(&self, _addr: ByteAddr) -> bool {
        true
    }

    // Check access for data store
    fn check_data_store(&self, _addr: ByteAddr) -> bool {
        true
    }
}

/// An implementation of the basic ISA (RV32IM), that is instruction decoding and functional units.
pub struct Emulator {}

#[derive(Debug)]
pub enum TrapCause {
    InstructionAddressMisaligned,
    InstructionAccessFault,
    IllegalInstruction(u32),
    Breakpoint,
    LoadAddressMisaligned,
    LoadAccessFault(ByteAddr),
    StoreAddressMisaligned(ByteAddr),
    StoreAccessFault,
    EcallError,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Instruction {
    pub kind: InsnKind,
    pub rd: RegIdx,
    pub rs1: RegIdx,
    pub rs2: RegIdx,
    pub imm: i64,
    /// Only to produce better logging and error messages.
    pub raw: Word,
}

#[derive(Clone, Copy, Debug)]
pub enum InsnCategory {
    Compute,
    Branch,
    Load,
    Store,
    System,
    Invalid,
}
use InsnCategory::*;

#[derive(Clone, Copy, Debug)]
pub enum InsnFormat {
    R,
    I,
    S,
    B,
    U,
    J,
}
use InsnFormat::*;

#[derive(
    Clone, Copy, Display, Debug, PartialEq, Eq, PartialOrd, Ord, EnumIter, ToPrimitive, Default,
)]
#[allow(clippy::upper_case_acronyms)]
pub enum InsnKind {
    #[default]
    INVALID,
    ADD,
    SUB,
    XOR,
    OR,
    AND,
    SLL,
    SRL,
    SRA,
    SLT,
    SLTU,
    ADDI,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    SLTI,
    SLTIU,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    JAL,
    JALR,
    MUL,
    MULH,
    MULHSU,
    MULHU,
    DIV,
    DIVU,
    REM,
    REMU,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    ECALL,
    EBREAK,
}
use InsnKind::*;

impl From<InsnKind> for InsnCategory {
    fn from(kind: InsnKind) -> Self {
        // TODO: double check this.
        // Perhaps get it via a macro from RV32IM_ISA.
        match kind {
            INVALID => Invalid,
            ADD | SUB | XOR | OR | AND | SLL | SRL | SRA | SLT | SLTU | MUL | MULH | MULHSU
            | MULHU | DIV | DIVU | REM | REMU => Compute,
            ADDI | XORI | ORI | ANDI | SLLI | SRLI | SRAI | SLTI | SLTIU => Compute,
            BEQ | BNE | BLT | BGE | BLTU | BGEU => Branch,
            JAL | JALR => Compute,
            LB | LH | LW | LBU | LHU => Load,
            SB | SH | SW => Store,
            ECALL | EBREAK => System,
        }
    }
}

// For encoding, which is useful for tests.
impl From<InsnKind> for InsnFormat {
    fn from(kind: InsnKind) -> Self {
        match kind {
            // TODO(Matthias): review this list.
            ADD | SUB | XOR | OR | AND | SLL | SRL | SRA | SLT | SLTU | MUL | MULH | MULHSU
            | MULHU | DIV | DIVU | REM | REMU => R,
            ADDI | XORI | ORI | ANDI | SLLI | SRLI | SRAI | SLTI | SLTIU => I,
            BEQ | BNE | BLT | BGE | BLTU | BGEU => B,
            JAL | JALR => J,
            LB | LH | LW | LBU | LHU => I,
            SB | SH | SW => S,
            ECALL | EBREAK => I,
            INVALID => I,
        }
    }
}

impl Instruction {
    pub const RD_NULL: u32 = 32;
    pub fn rd_internal(&self) -> u32 {
        match InsnFormat::from(self.kind) {
            R | I | U | J if self.rd != 0 => self.rd as u32,
            _ => Self::RD_NULL,
        }
    }
    // TODO(Matthias): review return type
    /// Get the register source 1, or zero if the instruction does not use rs1.
    pub fn rs1_or_zero(&self) -> u32 {
        match InsnFormat::from(self.kind) {
            R | I | S | B => self.rs1 as u32,
            _ => 0,
        }
    }
    // TODO(Matthias): review return type
    /// Get the register source 2, or zero if the instruction does not use rs2.
    pub fn rs2_or_zero(&self) -> u32 {
        match InsnFormat::from(self.kind) {
            R | S | B => self.rs2 as u32,
            _ => 0,
        }
    }
}

impl Emulator {
    pub fn step<C: EmuContext>(&self, ctx: &mut C) -> Result<()> {
        let pc = ctx.get_pc();

        let Some(insn) = ctx.fetch(pc.waddr()) else {
            ctx.trap(TrapCause::InstructionAccessFault)?;
            return Err(anyhow!(
                "Fatal: could not fetch instruction at pc={pc:?}, ELF does not have instructions there."
            ));
        };

        tracing::trace!("pc: {:x}, kind: {:?}", pc.0, insn.kind);

        if match InsnCategory::from(insn.kind) {
            InsnCategory::Compute => self.step_compute(ctx, insn.kind, &insn)?,
            InsnCategory::Branch => self.step_branch(ctx, insn.kind, &insn)?,
            InsnCategory::Load => self.step_load(ctx, insn.kind, &insn)?,
            InsnCategory::Store => self.step_store(ctx, insn.kind, &insn)?,
            InsnCategory::System => self.step_system(ctx, insn.kind, &insn)?,
            InsnCategory::Invalid => ctx.trap(TrapCause::IllegalInstruction(insn.raw))?,
        } {
            ctx.on_normal_end(&insn);
        };

        Ok(())
    }

    fn step_compute<M: EmuContext>(
        &self,
        ctx: &mut M,
        kind: InsnKind,
        decoded: &Instruction,
    ) -> Result<bool> {
        use InsnKind::*;

        let pc = ctx.get_pc();
        let mut new_pc = pc + WORD_SIZE;
        let imm_i = decoded.imm as u32;
        let out = match kind {
            // Instructions that do not read rs1 nor rs2.
            JAL => {
                new_pc = pc.wrapping_add(decoded.imm as u32);
                (pc + WORD_SIZE).0
            }
            _ => {
                // Instructions that read rs1 but not rs2.
                let rs1 = ctx.load_register(decoded.rs1)?;

                match kind {
                    ADDI => rs1.wrapping_add(imm_i),
                    XORI => rs1 ^ imm_i,
                    ORI => rs1 | imm_i,
                    ANDI => rs1 & imm_i,
                    SLLI => rs1.wrapping_mul(imm_i),
                    SRLI => rs1.wrapping_div(imm_i),
                    // TODO(Matthias): check this.
                    SRAI => (rs1 as i32).wrapping_div(imm_i as i32) as u32,
                    SLTI => {
                        if (rs1 as i32) < (imm_i as i32) {
                            1
                        } else {
                            0
                        }
                    }
                    SLTIU => {
                        if rs1 < imm_i {
                            1
                        } else {
                            0
                        }
                    }
                    JALR => {
                        new_pc = ByteAddr(rs1.wrapping_add(imm_i) & 0xfffffffe);
                        (pc + WORD_SIZE).0
                    }

                    _ => {
                        // Instructions that use rs1 and rs2.
                        let rs2 = ctx.load_register(decoded.rs2)?;

                        match kind {
                            ADD => rs1.wrapping_add(rs2),
                            SUB => rs1.wrapping_sub(rs2),
                            XOR => rs1 ^ rs2,
                            OR => rs1 | rs2,
                            AND => rs1 & rs2,
                            SLL => rs1 << (rs2 & 0x1f),
                            SRL => rs1 >> (rs2 & 0x1f),
                            SRA => ((rs1 as i32) >> (rs2 & 0x1f)) as u32,
                            SLT => {
                                if (rs1 as i32) < (rs2 as i32) {
                                    1
                                } else {
                                    0
                                }
                            }
                            SLTU => {
                                if rs1 < rs2 {
                                    1
                                } else {
                                    0
                                }
                            }
                            MUL => rs1.wrapping_mul(rs2),
                            MULH => {
                                (sign_extend_u32(rs1).wrapping_mul(sign_extend_u32(rs2)) >> 32)
                                    as u32
                            }
                            MULHSU => (sign_extend_u32(rs1).wrapping_mul(rs2 as i64) >> 32) as u32,
                            MULHU => (((rs1 as u64).wrapping_mul(rs2 as u64)) >> 32) as u32,
                            DIV => {
                                if rs2 == 0 {
                                    u32::MAX
                                } else {
                                    ((rs1 as i32).wrapping_div(rs2 as i32)) as u32
                                }
                            }
                            DIVU => {
                                if rs2 == 0 {
                                    u32::MAX
                                } else {
                                    rs1 / rs2
                                }
                            }
                            REM => {
                                if rs2 == 0 {
                                    rs1
                                } else {
                                    ((rs1 as i32).wrapping_rem(rs2 as i32)) as u32
                                }
                            }
                            REMU => {
                                if rs2 == 0 {
                                    rs1
                                } else {
                                    rs1 % rs2
                                }
                            }

                            _ => unreachable!("Illegal compute instruction: {:?}", kind),
                        }
                    }
                }
            }
        };
        if !new_pc.is_aligned() {
            return ctx.trap(TrapCause::InstructionAddressMisaligned);
        }
        ctx.store_register(decoded.rd_internal() as usize, out)?;
        ctx.set_pc(new_pc);
        Ok(true)
    }

    fn step_branch<M: EmuContext>(
        &self,
        ctx: &mut M,
        kind: InsnKind,
        decoded: &Instruction,
    ) -> Result<bool> {
        use InsnKind::*;

        let pc = ctx.get_pc();
        let rs1 = ctx.load_register(decoded.rs1 as RegIdx)?;
        let rs2 = ctx.load_register(decoded.rs2 as RegIdx)?;

        let taken = match kind {
            BEQ => rs1 == rs2,
            BNE => rs1 != rs2,
            BLT => (rs1 as i32) < (rs2 as i32),
            BGE => (rs1 as i32) >= (rs2 as i32),
            BLTU => rs1 < rs2,
            BGEU => rs1 >= rs2,
            _ => unreachable!("Illegal branch instruction: {:?}", kind),
        };

        let new_pc = if taken {
            pc.wrapping_add(decoded.imm as u32)
        } else {
            pc + WORD_SIZE
        };

        if !new_pc.is_aligned() {
            return ctx.trap(TrapCause::InstructionAddressMisaligned);
        }
        ctx.set_pc(new_pc);
        Ok(true)
    }

    fn step_load<M: EmuContext>(
        &self,
        ctx: &mut M,
        kind: InsnKind,
        decoded: &Instruction,
    ) -> Result<bool> {
        let rs1 = ctx.load_register(decoded.rs1)?;
        // LOAD instructions do not read rs2.
        let addr = ByteAddr(rs1.wrapping_add(decoded.imm as u32));
        if !ctx.check_data_load(addr) {
            return ctx.trap(TrapCause::LoadAccessFault(addr));
        }
        let data = ctx.load_memory(addr.waddr())?;
        let shift = 8 * (addr.0 & 3);
        let out = match kind {
            InsnKind::LB => {
                let mut out = (data >> shift) & 0xff;
                if out & 0x80 != 0 {
                    out |= 0xffffff00;
                }
                out
            }
            InsnKind::LH => {
                if addr.0 & 0x01 != 0 {
                    return ctx.trap(TrapCause::LoadAddressMisaligned);
                }
                let mut out = (data >> shift) & 0xffff;
                if out & 0x8000 != 0 {
                    out |= 0xffff0000;
                }
                out
            }
            InsnKind::LW => {
                if addr.0 & 0x03 != 0 {
                    return ctx.trap(TrapCause::LoadAddressMisaligned);
                }
                data
            }
            InsnKind::LBU => (data >> shift) & 0xff,
            InsnKind::LHU => {
                if addr.0 & 0x01 != 0 {
                    return ctx.trap(TrapCause::LoadAddressMisaligned);
                }
                (data >> shift) & 0xffff
            }
            _ => unreachable!(),
        };
        ctx.store_register(decoded.rd_internal() as usize, out)?;
        ctx.set_pc(ctx.get_pc() + WORD_SIZE);
        Ok(true)
    }

    fn step_store<M: EmuContext>(
        &self,
        ctx: &mut M,
        kind: InsnKind,
        decoded: &Instruction,
    ) -> Result<bool> {
        let rs1 = ctx.load_register(decoded.rs1)?;
        let rs2 = ctx.load_register(decoded.rs2)?;
        let addr = ByteAddr(rs1.wrapping_add(decoded.imm as u32));
        let shift = 8 * (addr.0 & 3);
        if !ctx.check_data_store(addr) {
            tracing::error!("mstore: addr={:x?},rs1={:x}", addr, rs1);
            return ctx.trap(TrapCause::StoreAccessFault);
        }
        let mut data = ctx.peek_memory(addr.waddr());
        match kind {
            InsnKind::SB => {
                data ^= data & (0xff << shift);
                data |= (rs2 & 0xff) << shift;
            }
            InsnKind::SH => {
                if addr.0 & 0x01 != 0 {
                    tracing::debug!("Misaligned SH");
                    return ctx.trap(TrapCause::StoreAddressMisaligned(addr));
                }
                data ^= data & (0xffff << shift);
                data |= (rs2 & 0xffff) << shift;
            }
            InsnKind::SW => {
                if addr.0 & 0x03 != 0 {
                    tracing::debug!("Misaligned SW");
                    return ctx.trap(TrapCause::StoreAddressMisaligned(addr));
                }
                data = rs2;
            }
            _ => unreachable!(),
        }
        ctx.store_memory(addr.waddr(), data)?;
        ctx.set_pc(ctx.get_pc() + WORD_SIZE);
        Ok(true)
    }

    fn step_system<M: EmuContext>(
        &self,
        ctx: &mut M,
        kind: InsnKind,
        decoded: &Instruction,
    ) -> Result<bool> {
        match kind {
            InsnKind::ECALL => ctx.ecall(),
            InsnKind::EBREAK => ctx.trap(TrapCause::Breakpoint),
            _ => ctx.trap(TrapCause::IllegalInstruction(decoded.raw)),
        }
    }
}

fn sign_extend_u32(x: u32) -> i64 {
    (x as i32) as i64
}
