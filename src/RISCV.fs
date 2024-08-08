// hyggec - The didactic compiler for the Hygge programming language.
// Copyright (C) 2023 Technical University of Denmark
// Author: Alceste Scalas <alcsc@dtu.dk>
// Released under the MIT license (see LICENSE.md for details)

/// Type definitions and functions for generating RISC-V assembly code.
/// This module covers RV32IMF: RISC-V 32-bit integer instructions (RV32I) plus
/// extensions for integer multiplication and division (M), and
/// single-precision floating-point (F).
module RISCV


/// Representation of a RISC-V general-purpose integer register, with static
/// methods for conventional symbolic names (zero, ra, sp, ...).
/// 
/// NOTE: the program counter register (PC) is not included here, since it
/// cannot be directly read/written with load/store instructions.
[<RequireQualifiedAccess>]
type Reg (n: uint) =
    do if (n > 31u) then failwith $"BUG: requesting invalid register %u{n}"

    member this.Number = n

    // fsharplint:disable memberNames
    static member zero = Reg(0u)
    static member ra = Reg(1u)
    static member sp = Reg(2u)
    static member gp = Reg(3u)
    static member tp = Reg(4u)
    static member t0 = Reg(5u)
    static member t1 = Reg(6u)
    static member t2 = Reg(7u)
    static member fp = Reg(8u)
    static member s0 = Reg(8u)
    static member s1 = Reg(9u)
    static member a0 = Reg(10u)
    static member a1 = Reg(11u)
    static member a2 = Reg(12u)
    static member a3 = Reg(13u)
    static member a4 = Reg(14u)
    static member a5 = Reg(15u)
    static member a6 = Reg(16u)
    static member a7 = Reg(17u)
    static member s2 = Reg(18u)
    static member s3 = Reg(19u)
    static member s4 = Reg(20u)
    static member s5 = Reg(21u)
    static member s6 = Reg(22u)
    static member s7 = Reg(23u)
    static member s8 = Reg(24u)
    static member s9 = Reg(25u)
    static member s10 = Reg(26u)
    static member s11 = Reg(27u)
    static member t3 = Reg(28u)
    static member t4 = Reg(29u)
    static member t5 = Reg(30u)
    static member t6 = Reg(31u)

    /// Temporary register, ranging over all 't' registers.
    static member t (n: uint): Reg =
        match n with
        | m when (m >= 0u) && (m <= 2u) -> Reg(m + 5u) // Maps to t0..t2
        | m when (m >= 3u) && (m <= 6u) -> Reg((m - 3u) + 28u) // Maps to t3..t6
        | x -> failwith $"BUG: invalid temporary register number %u{x}"

    /// Saved register, ranging over all 's' registers.
    static member s (n: uint): Reg =
        match n with
        | m when (m >= 0u) && (m <= 1u) -> Reg(m + 8u) // Maps to s0..t1
        | m when (m >= 2u) && (m <= 11u) -> Reg((m - 2u) + 18u) // Maps to s2..s11
        | x -> failwith $"BUG: invalid saved register number %u{x}"

    /// Function argument register, ranging over a0..a7.
    static member a (n: uint): Reg =
        match n with
        | m when (m >= 0u) && (m <= 7u) -> Reg(m + 10u) // Maps to a0..a7
        | x -> failwith $"BUG: invalid argument register number %u{x}"

    /// Generic register, ranging over all (callee-)saved and temporary
    /// (caller-saved) registers. NOTE: we do not use register s0, so it remains
    /// available as frame pointer (fp) if needed.
    static member r (n: uint): Reg =
        match n with
        | m when (m >= 0u) && (m <= 2u) -> Reg(m + 5u) // Maps to t0..t2
        | m when (m >= 3u) && (m <= 3u) -> Reg((m - 3u) + 9u) // Maps to s1
        | m when (m >= 4u) && (m <= 13u) -> Reg((m - 4u) + 18u) // Maps to s2..s11
        | m when (m >= 14u) && (m <= 17u) -> Reg((m - 14u) + 28u) // Maps to t3..t6
        | x -> failwith $"BUG: invalid generic register number %u{x}"

    // fsharplint:enable memberNames

    /// String representation of the register, using conventional RISC-V names.
    override this.ToString(): string =
        match this.Number with
        | 0u -> "zero"
        | 1u -> "ra"
        | 2u -> "sp"
        | 3u -> "gp"
        | 4u -> "tp"
        | m when (m >= 5u) && (m <= 7u) -> $"t%u{m - 5u}"
        | 8u -> "fp"
        | m when (m >= 8u) && (m <= 9u) -> $"s%u{m - 8u}"
        | m when (m >= 10u) && (m <= 17u) -> $"a%u{m - 10u}"
        | m when (m >= 18u) && (m <= 27u) -> $"s%u{(m - 18u) + 2u}"
        | m when (m >= 28u) && (m <= 31u) -> $"t%u{(m - 28u) + 3u}"
        | x -> failwith $"BUG: register instantiated with invalid number %u{x}"

    // Various verrides to implement F# 'comparison' on this type
    override this.Equals (o: obj): bool = this.Number = (o :?> Reg).Number
    override this.GetHashCode(): int = int(this.Number)
    interface System.IComparable<Reg> with
        member this.CompareTo(r: Reg) = compare this.Number r.Number
    interface System.IComparable with
        member this.CompareTo(o: obj) = compare this.Number (o :?> Reg).Number


/// Representation of a RISC-V floating-point register, with static methods for
/// conventional symbolic names (ft0-ft7, fs0-fs1,...)
[<RequireQualifiedAccess>]
type FPReg (n: uint) =
    do if (n > 31u) then failwith $"BUG: requesting invalid register %u{n}"

    member this.Number = n

    // fsharplint:disable memberNames
    static member ft0 = FPReg(0u)
    static member ft1 = FPReg(1u)
    static member ft2 = FPReg(2u)
    static member ft3 = FPReg(3u)
    static member ft4 = FPReg(4u)
    static member ft5 = FPReg(5u)
    static member ft6 = FPReg(6u)
    static member ft7 = FPReg(7u)
    static member fs0 = FPReg(8u)
    static member fs1 = FPReg(9u)
    static member fa0 = FPReg(10u)
    static member fa1 = FPReg(11u)
    static member fa2 = FPReg(12u)
    static member fa3 = FPReg(13u)
    static member fa4 = FPReg(14u)
    static member fa5 = FPReg(15u)
    static member fa6 = FPReg(16u)
    static member fa7 = FPReg(17u)
    static member fs2 = FPReg(18u)
    static member fs3 = FPReg(19u)
    static member fs4 = FPReg(20u)
    static member fs5 = FPReg(21u)
    static member fs6 = FPReg(22u)
    static member fs7 = FPReg(23u)
    static member fs8 = FPReg(24u)
    static member fs9 = FPReg(25u)
    static member fs10 = FPReg(26u)
    static member fs11 = FPReg(27u)
    static member ft8 = FPReg(28u)
    static member ft9 = FPReg(29u)
    static member ft10 = FPReg(30u)
    static member ft11 = FPReg(31u)

    /// Temporary floating-point register, ranging over 'ft' registers.
    static member ft (n: uint): FPReg =
        match n with
        | m when (m >= 0u) && (m <= 7u) -> FPReg(m) // Maps to ft0..ft7
        | m when (m >= 8u) && (m <= 11u) -> FPReg((m - 8u) + 28u) // Maps to ft8..ft11
        | x -> failwith $"BUG: invalid temporary floating-point register number %u{x}"

    /// Saved floating-point register, ranging over 'fs' registers.
    static member fs (n: uint): FPReg =
        match n with
        | m when (m >= 0u) && (m <= 1u) -> FPReg(m + 8u) // Maps to fs0..fs1
        | m when (m >= 2u) && (m <= 11u) -> FPReg((m - 2u) + 18u) // Maps to ft8..ft11
        | x -> failwith $"BUG: invalid temporary floating-point register number %u{x}"

    /// Floating-point function argument register, ranging over fa0..fa7
    static member fa (n: uint): FPReg =
        match n with
        | m when (m >= 0u) && (m <= 7u) -> FPReg(m + 10u) // Maps to fa0..fa7
        | x -> failwith $"BUG: invalid floating-point argument register number %u{x}"

    /// Generic floating-point register, ranging over all 'fs' and 'ft' registers.
    static member r (n: uint): FPReg =
        match n with
        | m when (m >= 0u) && (m <= 9u) -> FPReg(m) // Maps to ft0..ft7 and fs0..fs1
        | m when (m >= 10u) && (m <= 23u) -> FPReg(m + 8u) // Maps to fs2..fs11 and ft8..ft11
        | x -> failwith $"BUG: invalid generic floating-point register number %u{x}"

    // fsharplint:enable memberNames

    /// String representation of the register, using conventional RISC-V names.
    override this.ToString(): string =
        match this.Number with
        | m when (m <= 7u) -> $"ft%u{m}"
        | m when (m >= 8u) && (m <= 9u) -> $"fs%u{m - 8u}"
        | m when (m >= 10u) && (m <= 17u) -> $"fa%u{m - 10u}"
        | m when (m >= 18u) && (m <= 27u) -> $"fs%u{(m - 18u) + 2u}"
        | m when (m >= 28u) && (m <= 31u) -> $"ft%u{(m - 28u) + 8u}"
        | x -> failwith $"BUG: floating-point register instantiated with invalid number %u{x}"

    // Various verrides to implement F# 'comparison' on this type
    override this.Equals (o: obj): bool = this.Number = (o :?> FPReg).Number
    override this.GetHashCode(): int = int(this.Number)
    interface System.IComparable<FPReg> with
        member this.CompareTo(r: FPReg) = compare this.Number r.Number
    interface System.IComparable with
        member this.CompareTo(o: obj) = compare this.Number (o :?> FPReg).Number


/// Does the given integer fit in 12 bits?
let isImm12 (value: int32): bool =
    (value >= (-(2<<<(12-1)))) && ((value <= (2<<<(12-1)-1)))


/// Immediate signed integer value of 12 bits.
type Imm12 (value: int32) =
    do if not (isImm12 value)
        then failwith $"BUG: out-of-range imm12: %d{value}"
    member this.Value = value

    /// Return the string representation of this integer value.
    override this.ToString(): string = $"%d{this.Value}"


/// Does the given unsigned integer fit in 12 bits?
let isImm12U (value: uint32): bool =
    value <= (2u<<<12)


/// Immediate unsigned integer value of 12 bits.
type Imm12U (value: uint32) =
    do if not (isImm12U value)
        then failwith $"BUG: out-of-range unsigned imm12: %u{value}"
    member this.Value = value

    /// Return the string representation of this integer value.
    override this.ToString(): string = $"%u{this.Value}"


/// Does the given integer fit in 20 bits?
let isImm20 (value: int32): bool =
    (value >= (-(2<<<(20-1)))) && ((value <= (2<<<(20-1)-1)))


/// Immediate integer value of 20 bits.
type Imm20 (value: int32) =
    do if not (isImm20 value)
        then failwith $"BUG: out-of-range imm20: %d{value}"
    member this.Value = value

    /// Return the string representation of this integer value.
    override this.ToString(): string = $"%d{this.Value}"


/// Logical shift amount: an unsigned integer value of 5 bits.
type Shamt (value: uint32) =
    do if (value > (2u<<<5)) then failwith $"BUG: out-of-range shamt: %u{value}"
    member this.Value = value

    /// Return the string representation of this integer value.
    override this.ToString(): string = $"%u{this.Value}"


/// Representation of a RISC-V asembly statement.  ('RV' stands for 'RISC-V'.)
[<RequireQualifiedAccess>]
type RV =
    // Pseudo-instructions
    | LI of rd: Reg * imm: int32
    | LA of rd: Reg * symbol: string
    | MV of rd: Reg * rs: Reg
    | NOT of rd: Reg * rs: Reg
    | NEG of rd: Reg * rs: Reg
    | BGT of rs: Reg * rt: Reg * label: string
    | BGTU of rs: Reg * rt: Reg * label: string
    | BLE of rs: Reg * rt: Reg * label: string
    | BLEU of rs: Reg * rt: Reg * label: string
    | BEQZ of rs: Reg * label: string
    | BNEZ of rs: Reg * label: string
    | BGEZ of rs: Reg * label: string
    | BLTZ of rs: Reg * label: string
    | BLEZ of rs: Reg * label: string
    | BGTZ of rs: Reg * label: string
    | SNEZ of rd: Reg * rs: Reg
    | SEQZ of rd: Reg * rs: Reg
    | J of label: string
    | CALL of label: string
    | TAIL of label: string
    | RET of label: string
    | NOP
    // Arithmetic instructions
    | ADD of rd: Reg * rs1: Reg * rs2: Reg
    | SUB of rd: Reg * rs1: Reg * rs2: Reg
    | ADDI of rd: Reg * rs1: Reg * imm12: Imm12
    | SLT of rd: Reg * rs1: Reg * rs2: Reg
    | SLTI of rd: Reg * rs1: Reg * imm12: Imm12
    | SLTU of rd: Reg * rs1: Reg * rs2: Reg
    | SLTIU of rd: Reg * rs1: Reg * imm12: Imm12U
    | LUI of rd: Reg * imm20: Imm20
    | AUIPC of rd: Reg * imm20: Imm20
    // RV32M Standard Extension for Integer Multiply and Divide
    | MUL of rd: Reg * rs1: Reg * rs2: Reg
    | MULH of rd: Reg * rs1: Reg * rs2: Reg
    | MULHSU of rd: Reg * rs1: Reg * rs2: Reg
    | MULHU of rd: Reg * rs1: Reg * rs2: Reg
    | DIV of rd: Reg * rs1: Reg * rs2: Reg
    | DIVU of rd: Reg * rs1: Reg * rs2: Reg
    | REM of rd: Reg * rs1: Reg * rs2: Reg
    | REMU of rd: Reg * rs1: Reg * rs2: Reg
    // Logical instructions
    | AND of rd: Reg * rs1: Reg * rs2: Reg
    | OR of rd: Reg * rs1: Reg * rs2: Reg
    | XOR of rd: Reg * rs1: Reg * rs2: Reg
    | ANDI of rd: Reg * rs1: Reg * imm12: Imm12
    | ORI of rd: Reg * rs1: Reg * imm12: Imm12
    | XORI of rd: Reg * rs1: Reg * imm12: Imm12
    | SLL of rd: Reg * rs1: Reg * rs2: Reg
    | SRL of rd: Reg * rs1: Reg * rs2: Reg
    | SRA of rd: Reg * rs1: Reg * rs2: Reg
    | SLLI of rd: Reg * rs1: Reg * shamt: Shamt
    | SRLI of rd: Reg * rs1: Reg * shamt: Shamt
    | SRAI of rd: Reg * rs1: Reg * shamt: Shamt
    // Data transfer instructions
    | LW of rd: Reg * imm12: Imm12 * rs1: Reg
    | LH of rd: Reg * imm12: Imm12 * rs1: Reg
    | LB of rd: Reg * imm12: Imm12 * rs1: Reg
    | LWU of rd: Reg * imm12: Imm12U * rs1: Reg
    | LHU of rd: Reg * imm12: Imm12U * rs1: Reg
    | LBU of rd: Reg * imm12: Imm12U * rs1: Reg
    | SW of rs2: Reg * imm12: Imm12 * rs1: Reg
    | SH of rs2: Reg * imm12: Imm12 * rs1: Reg
    | SB of rs2: Reg * imm12: Imm12 * rs1: Reg
    // Control transfer instructions
    | BEQ of rs1: Reg * rs2: Reg * label: string
    | BNE of rs1: Reg * rs2: Reg * label: string
    | BGE of rs1: Reg * rs2: Reg * label: string
    | BGEU of rs1: Reg * rs2: Reg * label: string
    | BLT of rs1: Reg * rs2: Reg * label: string
    | BLTU of rs1: Reg * rs2: Reg * label: string
    | JR of rs: Reg
    | JAL of rd: Reg * label: string
    | JALR of rd: Reg * imm12: Imm12 * rs1: Reg
    // System instructions
    | ECALL
    | EBREAK
    // Single-precision floating-point extension: load & store instructions
    | FLW_S of rd: FPReg * imm12: Imm12 * rs1: Reg
    | FSW_S of rs2: FPReg * imm12: Imm12 * rs1: Reg
    | FMV_S of rd: FPReg * rs: FPReg
    // Single-precision floating-point extension: computation instructions
    | FADD_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FSUB_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FMUL_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FDIV_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FMIN_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FMAX_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FMADD_S of rd: FPReg * rs1: FPReg * rs2: FPReg * rs3: FPReg
    | FMSUB_S of rd: FPReg * rs1: FPReg * rs2: FPReg * rs3: FPReg
    | FNMADD_S of rd: FPReg * rs1: FPReg * rs2: FPReg * rs3: FPReg
    | FNMSUB_S of rd: FPReg * rs1: FPReg * rs2: FPReg * rs3: FPReg
    | FSQRT_S of rd: FPReg * rs: FPReg
    // Single-precision floating-point extension: conversion instructions
    | FCVT_W_S of rd: Reg * rs: FPReg
    | FCVT_WU_S of rd: Reg * rs: FPReg
    | FCVT_S_W of rd: FPReg * rs: Reg
    | FCVT_S_WU of rd: FPReg * rs: Reg
    | FSGNJ_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FSGNJN_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FSGNJX_S of rd: FPReg * rs1: FPReg * rs2: FPReg
    | FMV_X_W of rd: Reg * rs: FPReg
    | FMV_W_X of rd: FPReg * rs: Reg
    // Single-precision floating-point extension: compare instructions
    | FEQ_S of rd: Reg * rs1: FPReg * rs2: FPReg
    | FLT_S of rd: Reg * rs1: FPReg * rs2: FPReg
    | FLE_S of rd: Reg * rs1: FPReg * rs2: FPReg
    // Single-precision floating-point extension: classification instructions
    | FCLASS_S of rd: Reg * rs: FPReg
    // Insert a label in the generated assembly (not really an instruction)
    | LABEL of label: string
    // Insert a label in the generated assembly (not really an instruction)
    | COMMENT of text: string

    /// String representation of this RISC-V assembly statement.
    override this.ToString(): string =
        match this with
        | LI(rd, imm) -> $"li %O{rd}, %d{imm}"
        | LA(rd, symbol) -> $"la %O{rd}, %s{symbol}"
        | MV(rd, rs) ->  $"mv %O{rd}, %O{rs}"
        | NOT(rd, rs) -> $"not %O{rd}, %O{rs}"
        | NEG(rd, rs) -> $"neg %O{rd}, %O{rs}"
        | BGT(rs, rt, label) -> $"bgt %O{rs}, %O{rt}, %s{label}"
        | BGTU(rs, rt, label) -> $"bgtu %O{rs}, %O{rt}, %s{label}"
        | BLE(rs, rt, label) -> $"ble %O{rs}, %O{rt}, %s{label}"
        | BLEU(rs, rt, label) -> $"bleu %O{rs}, %O{rt}, %s{label}"
        | BEQZ(rs, label) -> $"beqz %O{rs}, %s{label}"
        | BNEZ(rs, label) -> $"bnez %O{rs}, %s{label}"
        | BGEZ(rs, label) -> $"bgez %O{rs}, %s{label}"
        | BLTZ(rs, label) -> $"bltz %O{rs}, %s{label}"
        | BLEZ(rs, label) -> $"blez %O{rs}, %s{label}"
        | BGTZ(rs, label) -> $"bgtz %O{rs}, %s{label}"
        | SNEZ(rd, rs) -> $"snez %O{rd}, %O{rs}"
        | SEQZ(rd, rs) -> $"seqz %O{rd}, %O{rs}"
        | J(label) -> $"j %s{label}"
        | CALL(label) -> $"call %s{label}"
        | TAIL(label) -> $"tail %s{label}"
        | RET(label) -> $"ret %s{label}"
        | NOP -> "nop"
        | ADD(rd, rs1, rs2) -> $"add %O{rd}, %O{rs1}, %O{rs2}"
        | SUB(rd, rs1, rs2) -> $"sub %O{rd}, %O{rs1}, %O{rs2}"
        | ADDI(rd, rs1, imm12) -> $"addi %O{rd}, %O{rs1}, %O{imm12}"
        | SLT(rd, rs1, rs2) -> $"slt %O{rd}, %O{rs1}, %O{rs2}"
        | SLTI(rd, rs1, imm12) -> $"slti %O{rd}, %O{rs1}, %O{imm12}"
        | SLTU(rd, rs1, rs2) -> $"sltu %O{rd}, %O{rs1}, %O{rs2}"
        | SLTIU(rd, rs1, imm12) -> $"sltiu %O{rd}, %O{rs1}, %O{imm12}"
        | LUI(rd, imm20) -> $"lui %O{rd}, %O{imm20}"
        | AUIPC(rd, imm20) -> $"auipc %O{rd}, %O{imm20}"
        | MUL(rd, rs1, rs2) -> $"mul %O{rd}, %O{rs1}, %O{rs2}"
        | MULH(rd, rs1, rs2) -> $"mulh %O{rd}, %O{rs1}, %O{rs2}"
        | MULHSU(rd, rs1, rs2) -> $"mulhsu %O{rd}, %O{rs1}, %O{rs2}"
        | MULHU(rd, rs1, rs2) -> $"mulhu %O{rd}, %O{rs1}, %O{rs2}"
        | DIV(rd, rs1, rs2) -> $"div %O{rd}, %O{rs1}, %O{rs2}"
        | DIVU(rd, rs1, rs2) -> $"divu %O{rd}, %O{rs1}, %O{rs2}"
        | REM(rd, rs1, rs2) -> $"rem %O{rd}, %O{rs1}, %O{rs2}"
        | REMU(rd, rs1, rs2) -> $"remu %O{rd}, %O{rs1}, %O{rs2}"
        | AND(rd, rs1, rs2) -> $"and %O{rd}, %O{rs1}, %O{rs2}"
        | OR(rd, rs1, rs2) -> $"or %O{rd}, %O{rs1}, %O{rs2}"
        | XOR(rd, rs1, rs2) -> $"xor %O{rd}, %O{rs1}, %O{rs2}"
        | ANDI(rd, rs1, imm12) -> $"andi %O{rd}, %O{rs1}, %O{imm12}"
        | ORI(rd, rs1, imm12) -> $"ori %O{rd}, %O{rs1}, %O{imm12}"
        | XORI(rd, rs1, imm12) -> $"xori %O{rd}, %O{rs1}, %O{imm12}"
        | SLL(rd, rs1, rs2) -> $"sll %O{rd}, %O{rs1}, %O{rs2}"
        | SRL(rd, rs1, rs2) -> $"srl %O{rd}, %O{rs1}, %O{rs2}"
        | SRA(rd, rs1, rs2) -> $"sra %O{rd}, %O{rs1}, %O{rs2}"
        | SLLI(rd, rs1, shamt) -> $"slli %O{rd}, %O{rs1}, %O{shamt}"
        | SRLI(rd, rs1, shamt) -> $"srli %O{rd}, %O{rs1}, %O{shamt}"
        | SRAI(rd, rs1, shamt) -> $"srai %O{rd}, %O{rs1}, %O{shamt}"
        | LW(rd, imm12, rs1) -> $"lw %O{rd}, %O{imm12}(%O{rs1})"
        | LH(rd, imm12, rs1) -> $"lh %O{rd}, %O{imm12}(%O{rs1})"
        | LB(rd, imm12, rs1) -> $"lb %O{rd}, %O{imm12}(%O{rs1})"
        | LWU(rd, imm12, rs1) -> $"lwu %O{rd}, %O{imm12}(%O{rs1})"
        | LHU(rd, imm12, rs1) -> $"lhu %O{rd}, %O{imm12}(%O{rs1})"
        | LBU(rd, imm12, rs1) -> $"lbu %O{rd}, %O{imm12}(%O{rs1})"
        | SW(rs2, imm12, rs1) -> $"sw %O{rs2}, %O{imm12}(%O{rs1})"
        | SH(rs2, imm12, rs1) -> $"sh %O{rs2}, %O{imm12}(%O{rs1})"
        | SB(rs2, imm12, rs1) -> $"sb %O{rs2}, %O{imm12}(%O{rs1})"
        | BEQ(rs1, rs2, label) -> $"beq %O{rs1}, %O{rs2}, %s{label}"
        | BNE(rs1, rs2, label) -> $"bne %O{rs1}, %O{rs2}, %s{label}"
        | BGE(rs1, rs2, label) -> $"bge %O{rs1}, %O{rs2}, %s{label}"
        | BGEU(rs1, rs2, label) -> $"bgeu %O{rs1}, %O{rs2}, %s{label}"
        | BLT(rs1, rs2, label) -> $"blt %O{rs1}, %O{rs2}, %s{label}"
        | BLTU(rs1, rs2, label) -> $"bltu %O{rs1}, %O{rs2}, %s{label}"
        | JAL(rd, label) -> $"jal %O{rd}, %s{label}"
        | JR (rs) -> $"jr %O{rs}"
        | JALR(rd, imm12, rs1) -> $"jalr %O{rd}, %O{imm12}(%O{rs1})"
        | ECALL -> "ecall"
        | EBREAK -> "ebreak"
        | FLW_S(rd, imm12, rs1) -> $"flw %O{rd}, %O{imm12}(%O{rs1})"
        | FSW_S(rs2, imm12, rs1) -> $"fsw %O{rs2}, %O{imm12}(%O{rs1})"
        | FMV_S(rd, rs) -> $"fmv.s %O{rd}, %O{rs}"
        | FADD_S(rd, rs1, rs2) -> $"fadd.s %O{rd}, %O{rs1}, %O{rs2}"
        | FSUB_S(rd, rs1, rs2) -> $"fsub.s %O{rd}, %O{rs1}, %O{rs2}"
        | FMUL_S(rd, rs1, rs2) -> $"fmul.s %O{rd}, %O{rs1}, %O{rs2}"
        | FDIV_S(rd, rs1, rs2) -> $"fdiv.s %O{rd}, %O{rs1}, %O{rs2}"
        | FMIN_S(rd, rs1, rs2) -> $"fmin.s %O{rd}, %O{rs1}, %O{rs2}"
        | FMAX_S(rd, rs1, rs2) -> $"fmax.s %O{rd}, %O{rs1}, %O{rs2}"
        | FMADD_S(rd, rs1, rs2, rs3) -> $"fmadd.s %O{rd}, %O{rs1}, %O{rs2}, %O{rs3}"
        | FMSUB_S(rd, rs1, rs2, rs3) -> $"fmsub.s %O{rd}, %O{rs1}, %O{rs2}, %O{rs3}"
        | FNMADD_S(rd, rs1, rs2, rs3) -> $"fnmadd.s %O{rd}, %O{rs1}, %O{rs2}, %O{rs3}"
        | FNMSUB_S(rd, rs1, rs2, rs3) -> $"fnmsub.s %O{rd}, %O{rs1}, %O{rs2}, %O{rs3}"
        | FSQRT_S(rd, rs) -> $"fsqrt.s %O{rd}, %O{rs}"
        | FCVT_W_S(rd, rs) -> $"fcvt.w.s %O{rd}, %O{rs}"
        | FCVT_WU_S(rd, rs) -> $"fcvt.wu.s %O{rd}, %O{rs}"
        | FCVT_S_W(rd, rs) -> $"fcvt.s.w %O{rd}, %O{rs}"
        | FCVT_S_WU(rd, rs) -> $"fcvt.s.wu %O{rd}, %O{rs}"
        | FSGNJ_S(rd, rs1, rs2) -> $"fsgnj.s %O{rd}, %O{rs1}, %O{rs2}"
        | FSGNJN_S(rd, rs1, rs2) -> $"fsgnjn.s %O{rd}, %O{rs1}, %O{rs2}"
        | FSGNJX_S(rd, rs1, rs2) -> $"fsgnjx.s %O{rd}, %O{rs1}, %O{rs2}"
        | FMV_X_W(rd, rs) -> $"fmv.x.w %O{rd}, %O{rs}"
        | FMV_W_X(rd, rs) -> $"fmv.w.x %O{rd}, %O{rs}"
        | FEQ_S(rd, rs1, rs2) -> $"feq.s %O{rd}, %O{rs1}, %O{rs2}"
        | FLT_S(rd, rs1, rs2) -> $"flt.s %O{rd}, %O{rs1}, %O{rs2}"
        | FLE_S(rd, rs1, rs2) -> $"fle.s %O{rd}, %O{rs1}, %O{rs2}"
        | FCLASS_S(rd, rs) -> $"fclass %O{rd}, %O{rs}"
        | LABEL l -> $"%O{l}:"
        | COMMENT(text) -> $"# %s{text}"


/// Representation of a data allocation in the generated assembly code.
[<RequireQualifiedAccess>]
type Alloc =
    /// Allocation of a 32-bit word.
    | Word of init: int32
    /// Allocation of a string.
    | String of init: string

    override this.ToString(): string =
        match this with
        | Word(init) -> $".word 0x%x{init}"
        | String(init) -> $".string \"%s{init}\"" // FIXME: escape 'init'


/// A data segment statement: a triplet with label, size, and a comment.
type internal DataStmt = string * Alloc * string


/// A text segment statement: a tuple with an instruction and a comment.
type TextStmt = RV * string


/// Representation of assembly code, with methods to combine and manipulate
/// assembly code snippets. The constructor arguments denote respectively the
/// 'data', and 'text' segments of the assembly code under construction.
/// 'postText' is part of the text segment, but its content is rendered at the
/// end of the text segment itself.
[<RequireQualifiedAccess>]
type Asm private (data: list<DataStmt>, text: list<TextStmt>, postText: list<TextStmt>) =
    member private this.Data = data
    member private this.Text = text
    member private this.PostText = postText

    /// Create a new RISC-V assembly code fragment with the given list of
    /// instructions and comments in the Text segment.
    new(instrs: List<RV * string>) = Asm([], (List.rev instrs), [])

    /// Create a new empty RISC-V assembly code fragment.
    new() = Asm([])

    /// Create a new RISC-V assembly code fragment with the given instruction in
    /// the Text segment.
    new(op: RV) = Asm([(op, "")])

    /// Create a new RISC-V assembly code fragment with the given instruction
    /// and comment in the Text segment.
    new(op: RV, comment: string) = Asm([(op, comment)])

    /// Create a new RISC-V assembly code fragment by concatenating the data and
    /// text segments of the given fragments.  NOTE: the Data and Text segments
    /// of 'asm1' are placed before those of 'asm2', whereas the PostText
    /// segment of 'asm1' is placed after that of 'asm2'.
    static member (++) (asm1: Asm, asm2: Asm): Asm =
        Asm(asm2.Data @ asm1.Data, asm2.Text @ asm1.Text,
            asm1.PostText @ asm2.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by adding a
    /// new allocation (including a comment) to the data segment.
    member this.AddData (label: string, alloc: Alloc, comment: string): Asm =
        Asm((label, alloc, comment) :: this.Data, this.Text, this.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by adding a
    /// new allocation to the data segment.
    member this.AddData (label: string, alloc: Alloc): Asm =
        Asm((label, alloc, "") :: this.Data, this.Text, this.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by adding the
    /// given instruction to the text segment.
    member this.AddText (op: RV): Asm =
        Asm(this.Data, (op, "") :: this.Text, this.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by adding the
    /// given instruction (including a comment) to the text segment.
    member this.AddText (op: RV, comment: string): Asm =
        Asm(this.Data, (op, comment) :: this.Text, this.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by adding a
    /// list of instructions (each one including a comment) to the text segment.
    member this.AddText (instrs: List<RV * string>): Asm =
        Asm(this.Data, (List.rev instrs) @ this.Text, this.PostText)

    /// Create a new RISC-V assembly code fragment from this one, by moving the
    /// contents of its Text segment after its PostText.
    member this.TextToPostText: Asm =
        Asm(this.Data, [], this.Text @ this.PostText)

    /// Return the list of RISC-V assembly statements in the Text segment
    /// (including the "PostText").
    member this.GetText: List<TextStmt> =
        // Remember that the RISC-V instructions are stored in reverse order
        List.rev (this.PostText @ this.Text)

    /// Creat e new RISC-V assembly code fragment from this one, by replacing
    /// the contents of the Text segment (including the "PostText") with the
    /// given list of statements.
    member this.SetText (text: List<TextStmt>): Asm =
        // Remember that the RISC-V instructions are stored in reverse order
        Asm(this.Data, List.rev(text), [])

    /// Return the string representation of a Data segment.
    static member private DataToString (data: list<DataStmt>): string =
        let rec loop(data: list<DataStmt>) =
            match data with
            | [] -> ""
            | (label, alloc, "") :: ds ->
                $"%O{label}:%s{Util.nl}    %O{alloc}%s{Util.nl}" + (loop ds)
            | (label, alloc, comment) :: ds ->
                // FIXME: add support for multiline comments
                $"%O{label}:%s{Util.nl}    %O{alloc}  # %s{comment}%s{Util.nl}" + (loop ds)
        loop (List.rev data)

    /// Return the string representation of a Text segment.
    static member private TextToString (text: list<TextStmt>): string =
        let rec loop (text: list<TextStmt>) =
            match text with
            | [] -> ""
            | (op, optComment) :: ts ->
                let indent = match op with
                             | RV.LABEL(l) -> ""
                             | _ -> "    "
                let comment = match optComment with
                              | "" -> ""
                              | c -> $"  # %s{c}"
                // FIXME: add support for multiline comments
                $"%s{indent}%O{op}%s{comment}%s{Util.nl}" + (loop ts)
        loop (List.rev text)

    /// Return the string representation of this RISC-V assembly code fragment.
    override this.ToString(): string =
        let data = $".data:%s{Util.nl}%s{Asm.DataToString this.Data}"
        let text = $".text:%s{Util.nl}%s{Asm.TextToString this.Text}"
        let postText = $"%s{Util.nl}%s{Asm.TextToString this.PostText}"
        $"%s{data}%s{Util.nl}%s{text}%s{Util.nl}%s{postText}"
