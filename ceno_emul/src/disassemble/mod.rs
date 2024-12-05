use itertools::izip;
use rrs_lib::{
    InstructionProcessor,
    instruction_formats::{BType, IType, ITypeCSR, ITypeShamt, JType, RType, SType, UType},
    process_instruction,
};

use crate::rv32im::Instruction;

impl Instruction {
    pub fn make_unsigned_imm(self) -> Self {
        Self {
            imm: i64::from(self.imm as u32),
            ..self
        }
    }
    pub fn make_shift_imm(self) -> Self {
        Self {
            imm: 1 << (self.imm & 0x1F),
            ..self
        }
    }
}

type InsnKind = crate::rv32im::InsnKind;

/// A transpiler that converts the 32-bit encoded instructions into instructions.
pub(crate) struct InstructionTranspiler {
    pc: u32,
    word: u32,
}

impl Instruction {
    /// Create a new [`Instruction`] from an R-type instruction.
    #[must_use]
    pub const fn from_r_type(kind: InsnKind, dec_insn: &RType, raw: u32) -> Self {
        Self {
            kind,
            rd: dec_insn.rd,
            rs1: dec_insn.rs1,
            rs2: dec_insn.rs2,
            imm: 0,
            raw,
        }
    }

    /// Create a new [`Instruction`] from an I-type instruction.
    #[must_use]
    pub const fn from_i_type(kind: InsnKind, dec_insn: &IType, raw: u32) -> Self {
        Self {
            kind,
            rd: dec_insn.rd,
            rs1: dec_insn.rs1,
            imm: dec_insn.imm as i64,
            rs2: 0,
            raw,
        }
    }

    /// Create a new [`Instruction`] from an I-type instruction with a shamt.
    #[must_use]
    pub const fn from_i_type_shamt(kind: InsnKind, dec_insn: &ITypeShamt, raw: u32) -> Self {
        Self {
            kind,
            rd: dec_insn.rd,
            rs1: dec_insn.rs1,
            imm: dec_insn.shamt as i64,
            rs2: 0,
            raw,
        }
    }

    /// Create a new [`Instruction`] from an S-type instruction.
    #[must_use]
    pub const fn from_s_type(kind: InsnKind, dec_insn: &SType, raw: u32) -> Self {
        Self {
            kind,
            rd: 0,
            rs1: dec_insn.rs1,
            rs2: dec_insn.rs2,
            imm: dec_insn.imm as i64,
            raw,
        }
    }

    /// Create a new [`Instruction`] from a B-type instruction.
    #[must_use]
    pub const fn from_b_type(kind: InsnKind, dec_insn: &BType, raw: u32) -> Self {
        Self {
            kind,
            rd: 0,
            rs1: dec_insn.rs1,
            rs2: dec_insn.rs2,
            imm: dec_insn.imm as i64,
            raw,
        }
    }

    /// Create a new [`Instruction`] that is not implemented.
    #[must_use]
    pub const fn unimp(raw: u32) -> Self {
        Self {
            kind: InsnKind::INVALID,
            rd: 0,
            rs1: 0,
            rs2: 0,
            imm: 0,
            raw,
        }
    }
}

impl InstructionProcessor for InstructionTranspiler {
    type InstructionResult = Instruction;

    fn process_add(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::ADD, &dec_insn, self.word)
    }

    fn process_addi(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::ADD, &dec_insn, self.word)
    }

    fn process_sub(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SUB, &dec_insn, self.word)
    }

    fn process_xor(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::XOR, &dec_insn, self.word)
    }

    fn process_xori(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::XOR, &dec_insn, self.word)
    }

    fn process_or(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::OR, &dec_insn, self.word)
    }

    fn process_ori(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::OR, &dec_insn, self.word)
    }

    fn process_and(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::AND, &dec_insn, self.word)
    }

    fn process_andi(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::AND, &dec_insn, self.word)
    }

    fn process_sll(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SLL, &dec_insn, self.word)
    }

    fn process_slli(&mut self, dec_insn: ITypeShamt) -> Self::InstructionResult {
        Instruction::from_i_type_shamt(InsnKind::SLL, &dec_insn, self.word).make_shift_imm()
    }

    fn process_srl(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SRL, &dec_insn, self.word)
    }

    fn process_srli(&mut self, dec_insn: ITypeShamt) -> Self::InstructionResult {
        Instruction::from_i_type_shamt(InsnKind::SRL, &dec_insn, self.word).make_shift_imm()
    }

    fn process_sra(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SRA, &dec_insn, self.word)
    }

    fn process_srai(&mut self, dec_insn: ITypeShamt) -> Self::InstructionResult {
        Instruction::from_i_type_shamt(InsnKind::SRA, &dec_insn, self.word).make_shift_imm()
    }

    fn process_slt(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SLT, &dec_insn, self.word)
    }

    fn process_slti(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::SLT, &dec_insn, self.word)
    }

    fn process_sltu(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::SLTU, &dec_insn, self.word)
    }

    fn process_sltui(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::SLTU, &dec_insn, self.word).make_unsigned_imm()
    }

    fn process_lb(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::LB, &dec_insn, self.word)
    }

    fn process_lh(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::LH, &dec_insn, self.word)
    }

    fn process_lw(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::LW, &dec_insn, self.word)
    }

    fn process_lbu(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::LBU, &dec_insn, self.word)
    }

    fn process_lhu(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction::from_i_type(InsnKind::LHU, &dec_insn, self.word)
    }

    fn process_sb(&mut self, dec_insn: SType) -> Self::InstructionResult {
        Instruction::from_s_type(InsnKind::SB, &dec_insn, self.word)
    }

    fn process_sh(&mut self, dec_insn: SType) -> Self::InstructionResult {
        Instruction::from_s_type(InsnKind::SH, &dec_insn, self.word)
    }

    fn process_sw(&mut self, dec_insn: SType) -> Self::InstructionResult {
        Instruction::from_s_type(InsnKind::SW, &dec_insn, self.word)
    }

    fn process_beq(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BEQ, &dec_insn, self.word)
    }

    fn process_bne(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BNE, &dec_insn, self.word)
    }

    fn process_blt(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BLT, &dec_insn, self.word)
    }

    fn process_bge(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BGE, &dec_insn, self.word)
    }

    fn process_bltu(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BLTU, &dec_insn, self.word)
    }

    fn process_bgeu(&mut self, dec_insn: BType) -> Self::InstructionResult {
        Instruction::from_b_type(InsnKind::BGEU, &dec_insn, self.word)
    }

    fn process_jal(&mut self, dec_insn: JType) -> Self::InstructionResult {
        Instruction {
            kind: InsnKind::JAL,
            rd: dec_insn.rd,
            rs1: 0,
            rs2: 0,
            imm: dec_insn.imm as i64,
            raw: self.word,
        }
    }

    fn process_jalr(&mut self, dec_insn: IType) -> Self::InstructionResult {
        Instruction {
            kind: InsnKind::JALR,
            rd: dec_insn.rd,
            rs1: dec_insn.rs1,
            rs2: 0,
            imm: dec_insn.imm as i64,
            raw: self.word,
        }
    }

    fn process_lui(&mut self, dec_insn: UType) -> Self::InstructionResult {
        // LUI instructions are handled in a special way inside the zkVM.
        //
        // Notably, LUI instructions are converted to an ADDI instruction
        Instruction {
            kind: InsnKind::ADDI,
            rd: dec_insn.rd,
            rs1: 0,
            rs2: 0,
            imm: i64::from(dec_insn.imm as u32),
            raw: self.word,
        }
    }

    /// AUIPC instructions have the third operand set to imm << 12.
    /// If we have the pc, we can build the absolute address by adding the immediate value to the pc,
    /// and convert this to an ADDI?
    fn process_auipc(&mut self, dec_insn: UType) -> Self::InstructionResult {
        let pc = self.pc;
        Instruction {
            kind: InsnKind::ADDI,
            rd: dec_insn.rd,
            rs1: 0,
            rs2: 0,
            // TODO(Matthias): check whether/where we need to do the '<< 12' shift,
            // or whether it happens automatically.
            imm: (dec_insn.imm as i64).wrapping_add(pc as i64) as u32 as i64,
            raw: self.word,
        }
    }

    fn process_ecall(&mut self) -> Self::InstructionResult {
        Instruction {
            kind: InsnKind::ECALL,
            rd: 0,
            rs1: 0,
            rs2: 0,
            imm: 0,
            raw: self.word,
        }
    }

    fn process_ebreak(&mut self) -> Self::InstructionResult {
        Instruction {
            kind: InsnKind::EBREAK,
            rd: 0,
            rs1: 0,
            rs2: 0,
            imm: 0,
            raw: self.word,
        }
    }

    fn process_mul(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::MUL, &dec_insn, self.word)
    }

    fn process_mulh(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::MULH, &dec_insn, self.word)
    }

    fn process_mulhu(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::MULHU, &dec_insn, self.word)
    }

    fn process_mulhsu(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::MULHSU, &dec_insn, self.word)
    }

    fn process_div(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::DIV, &dec_insn, self.word)
    }

    fn process_divu(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::DIVU, &dec_insn, self.word)
    }

    fn process_rem(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::REM, &dec_insn, self.word)
    }

    fn process_remu(&mut self, dec_insn: RType) -> Self::InstructionResult {
        Instruction::from_r_type(InsnKind::REMU, &dec_insn, self.word)
    }

    fn process_csrrc(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_csrrci(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_csrrs(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_csrrsi(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_csrrw(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_csrrwi(&mut self, _: ITypeCSR) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_fence(&mut self, _: IType) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_mret(&mut self) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }

    fn process_wfi(&mut self) -> Self::InstructionResult {
        Instruction::unimp(self.word)
    }
}

/// Transpile the [`Instruction`]s from the 32-bit encoded instructions.
///
/// # Panics
///
/// This function will return an error if the [`Instruction`] cannot be processed.
#[must_use]
pub fn transpile(base: u32, instructions_u32: &[u32]) -> Vec<Instruction> {
    let mut instructions = Vec::new();
    for (pc, &word) in izip!(enumerate(base, 4), instructions_u32) {
        let instruction =
            process_instruction(&mut InstructionTranspiler { pc, word }, word).unwrap();
        instructions.push(instruction);
    }
    instructions
}

fn enumerate(start: u32, step: u32) -> impl Iterator<Item = u32> {
    std::iter::successors(Some(start), move |&i| Some(i + step))
}
