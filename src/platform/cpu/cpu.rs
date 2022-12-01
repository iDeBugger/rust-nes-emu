use super::{context::CPUContext, memory::CPUMemory};
use log::{debug, trace};

macro_rules! trace_operand {
    ($opcode:tt, $operand:tt) => {
        trace!("[{}] Operand: {:X?}", $opcode, $operand);
    };
}

macro_rules! trace_operand_value {
    ($opcode:tt, $value:tt) => {
        trace!("[{}] Operand value: {:#X?} ({})", $opcode, $value, $value);
    };
}

macro_rules! trace_register {
    ($opcode:tt, $register:expr) => {
        trace!(
            "[{}] Register {}: {:#X?} ({})",
            $opcode,
            stringify!($register).split('.').collect::<Vec<_>>()[1].to_uppercase(),
            $register,
            $register
        );
    };
}

macro_rules! trace_flags {
    ($opcode:tt, $register:expr) => {
        trace!("[{}] Flags: {:08b}", $opcode, $register);
    };
}

macro_rules! trace_execute {
    ($opcode:tt) => {
        trace!("[{}] Executing...", $opcode);
    };
}

#[derive(Debug)]
enum Register {
    A,
    X,
    Y,
    PC,
    S,
    P,
}

#[derive(Debug, Clone, Copy)]
enum AddrMode {
    Implicit,
    Immediate,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Relative,
    Indirect,
    IndirectX,
    IndirectY,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpCode {
    ORA,
    AND,
    EOR,
    ADC,
    STA,
    LDA,
    CMP,
    SBC,

    PHP,
    BPL,
    CLC,
    JSR,
    BIT,
    PLP,
    BMI,
    SEC,
    RTI,
    PHA,
    JMP,
    BVC,
    CLI,
    RTS,
    PLA,
    BVS,
    SEI,
    STY,
    DEY,
    BCC,
    TYA,
    LDY,
    TAY,
    BCS,
    CLV,
    CPY,
    INY,
    BNE,
    CLD,
    CPX,
    INX,
    BEQ,
    SED,

    ASL,
    ROL,
    LSR,
    ROR,
    STX,
    TXA,
    TXS,
    LDX,
    TAX,
    TSX,
    DEC,
    DEX,
    INC,
    NOP,

    BRK,
}

#[derive(Debug)]
enum Operand {
    Memory(u16),
    Offset(i8),
}

pub struct CPU {
    pub pc: u16,
    a: u8,
    x: u8,
    y: u8,
    s: u8,
    p: u8,
    mem: CPUMemory,
}

const STACK_BASE: u16 = 0x0100;

impl CPU {
    pub fn new() -> Self {
        let mem = CPUMemory::new();
        CPU {
            a: 0x0,
            x: 0x0,
            y: 0x0,
            pc: 0xFFFC,
            s: 0xFD,
            p: 0x34,
            mem,
        }
    }

    pub fn read_mem(&self, ctx: &mut CPUContext, address: u16) -> u8 {
        self.mem.read(ctx, address)
    }

    pub fn write_mem(&mut self, ctx: &mut CPUContext, address: u16, value: u8) {
        self.mem.write(ctx, address, value)
    }

    pub fn run_step(&mut self, ctx: &mut CPUContext, stop_at_loop: bool) -> bool {
        trace!("Running CPU step...");
        let old_pc = self.pc;

        let (opcode, addr_mode) = self.parse_operator(ctx);
        trace!(
            "Executing {:?} ({:?}) at {:#X?}",
            opcode,
            addr_mode,
            self.pc
        );
        match opcode {
            OpCode::ORA => self.do_ora(ctx, &addr_mode),
            OpCode::AND => self.do_and(ctx, &addr_mode),
            OpCode::EOR => self.do_eor(ctx, &addr_mode),
            OpCode::ADC => self.do_adc(ctx, &addr_mode),
            OpCode::STA => self.do_sta(ctx, &addr_mode),
            OpCode::LDA => self.do_lda(ctx, &addr_mode),
            OpCode::CMP => self.do_cmp(ctx, &addr_mode),
            OpCode::SBC => self.do_sbc(ctx, &addr_mode),

            OpCode::PHP => self.do_php(ctx, &addr_mode),
            OpCode::BPL => self.do_bpl(ctx, &addr_mode),
            OpCode::CLC => self.do_clc(ctx, &addr_mode),
            OpCode::JSR => self.do_jsr(ctx, &addr_mode),
            OpCode::BIT => self.do_bit(ctx, &addr_mode),
            OpCode::PLP => self.do_plp(ctx, &addr_mode),
            OpCode::BMI => self.do_bmi(ctx, &addr_mode),
            OpCode::SEC => self.do_sec(ctx, &addr_mode),
            OpCode::RTI => self.do_rti(ctx, &addr_mode),
            OpCode::PHA => self.do_pha(ctx, &addr_mode),
            OpCode::JMP => self.do_jmp(ctx, &addr_mode),
            OpCode::BVC => self.do_bvc(ctx, &addr_mode),
            OpCode::CLI => self.do_cli(ctx, &addr_mode),
            OpCode::RTS => self.do_rts(ctx, &addr_mode),
            OpCode::PLA => self.do_pla(ctx, &addr_mode),
            OpCode::BVS => self.do_bvs(ctx, &addr_mode),
            OpCode::SEI => self.do_sei(ctx, &addr_mode),
            OpCode::STY => self.do_sty(ctx, &addr_mode),
            OpCode::DEY => self.do_dey(ctx, &addr_mode),
            OpCode::BCC => self.do_bcc(ctx, &addr_mode),
            OpCode::TYA => self.do_tya(ctx, &addr_mode),
            OpCode::LDY => self.do_ldy(ctx, &addr_mode),
            OpCode::TAY => self.do_tay(ctx, &addr_mode),
            OpCode::BCS => self.do_bcs(ctx, &addr_mode),
            OpCode::CLV => self.do_clv(ctx, &addr_mode),
            OpCode::CPY => self.do_cpy(ctx, &addr_mode),
            OpCode::INY => self.do_iny(ctx, &addr_mode),
            OpCode::BNE => self.do_bne(ctx, &addr_mode),
            OpCode::CLD => self.do_cld(&addr_mode),
            OpCode::CPX => self.do_cpx(ctx, &addr_mode),
            OpCode::INX => self.do_inx(ctx, &addr_mode),
            OpCode::BEQ => self.do_beq(ctx, &addr_mode),
            OpCode::SED => self.do_sed(ctx, &addr_mode),

            OpCode::ASL => self.do_asl(ctx, &addr_mode),
            OpCode::ROL => self.do_rol(ctx, &addr_mode),
            OpCode::LSR => self.do_lsr(ctx, &addr_mode),
            OpCode::ROR => self.do_ror(ctx, &addr_mode),
            OpCode::STX => self.do_stx(ctx, &addr_mode),
            OpCode::TXA => self.do_txa(ctx, &addr_mode),
            OpCode::TXS => self.do_txs(ctx, &addr_mode),
            OpCode::LDX => self.do_ldx(ctx, &addr_mode),
            OpCode::TAX => self.do_tax(ctx, &addr_mode),
            OpCode::TSX => self.do_tsx(ctx, &addr_mode),
            OpCode::DEC => self.do_dec(ctx, &addr_mode),
            OpCode::DEX => self.do_dex(ctx, &addr_mode),
            OpCode::INC => self.do_inc(ctx, &addr_mode),
            OpCode::NOP => self.do_nop(&addr_mode),
            OpCode::BRK => self.do_interrupt(ctx),
        }

        if ![
            OpCode::JMP,
            OpCode::JSR,
            OpCode::RTS,
            OpCode::RTI,
            OpCode::BPL,
            OpCode::BMI,
            OpCode::BVC,
            OpCode::BVS,
            OpCode::BCC,
            OpCode::BCS,
            OpCode::BNE,
            OpCode::BEQ,
            OpCode::BRK,
        ]
        .contains(&opcode)
        {
            self.pc += match addr_mode {
                AddrMode::Implicit => 1,
                AddrMode::Immediate => 2,
                AddrMode::ZeroPage => 2,
                AddrMode::ZeroPageX => 2,
                AddrMode::ZeroPageY => 2,
                AddrMode::Absolute => 3,
                AddrMode::AbsoluteX => 3,
                AddrMode::AbsoluteY => 3,
                AddrMode::Relative => 2,
                AddrMode::Indirect => 3,
                AddrMode::IndirectX => 2,
                AddrMode::IndirectY => 2,
            }
        }

        if stop_at_loop && self.pc == old_pc {
            debug!("We are in a loop, Kowalsky!");
            return true;
        }

        return false;
    }

    pub fn get_carry_flag(&self) -> bool {
        self.p & 0b00000001 > 0
    }

    fn set_carry_flag(&mut self) {
        self.p |= 0b00000001
    }

    fn clear_carry_flag(&mut self) {
        self.p &= 0b11111110
    }

    pub fn get_zero_flag(&self) -> bool {
        self.p & 0b00000010 > 0
    }

    fn set_zero_flag(&mut self) {
        self.p |= 0b00000010
    }

    fn clear_zero_flag(&mut self) {
        self.p &= 0b11111101;
    }

    pub fn get_interrupt_disable_flag(&self) -> bool {
        self.p & 0b00000100 > 0
    }

    fn set_interrupt_disable_flag(&mut self) {
        self.p |= 0b00000100
    }

    fn clear_interrupt_disable_flag(&mut self) {
        self.p &= 0b11111011
    }

    pub fn get_decimal_flag(&self) -> bool {
        self.p & 0b00001000 > 0
    }

    fn set_decimal_flag(&mut self) {
        self.p |= 0b00001000
    }

    fn clear_decimal_flag(&mut self) {
        self.p &= 0b11110111
    }

    pub fn get_overflow_flag(&self) -> bool {
        self.p & 0b01000000 > 0
    }

    fn set_overflow_flag(&mut self) {
        self.p |= 0b01000000
    }

    fn clear_overflow_flag(&mut self) {
        self.p &= 0b10111111
    }

    pub fn get_negative_flag(&self) -> bool {
        self.p & 0b10000000 > 0
    }

    fn set_negative_flag(&mut self) {
        self.p |= 0b10000000
    }

    fn clear_negative_flag(&mut self) {
        self.p &= 0b01111111
    }

    fn parse_operator(&mut self, ctx: &mut CPUContext<'_, '_>) -> (OpCode, AddrMode) {
        let opcode_byte = self.mem.read(ctx, self.pc);
        match opcode_byte {
            // ORA
            0x01 => (OpCode::ORA, AddrMode::IndirectX),
            0x05 => (OpCode::ORA, AddrMode::ZeroPage),
            0x09 => (OpCode::ORA, AddrMode::Immediate),
            0x0D => (OpCode::ORA, AddrMode::Absolute),
            0x11 => (OpCode::ORA, AddrMode::IndirectY),
            0x15 => (OpCode::ORA, AddrMode::ZeroPageX),
            0x19 => (OpCode::ORA, AddrMode::AbsoluteY),
            0x1D => (OpCode::ORA, AddrMode::AbsoluteX),
            // AND
            0x21 => (OpCode::AND, AddrMode::IndirectX),
            0x25 => (OpCode::AND, AddrMode::ZeroPage),
            0x29 => (OpCode::AND, AddrMode::Immediate),
            0x2D => (OpCode::AND, AddrMode::Absolute),
            0x31 => (OpCode::AND, AddrMode::IndirectY),
            0x35 => (OpCode::AND, AddrMode::ZeroPageX),
            0x39 => (OpCode::AND, AddrMode::AbsoluteY),
            0x3D => (OpCode::AND, AddrMode::AbsoluteX),
            // EOR
            0x41 => (OpCode::EOR, AddrMode::IndirectX),
            0x45 => (OpCode::EOR, AddrMode::ZeroPage),
            0x49 => (OpCode::EOR, AddrMode::Immediate),
            0x4D => (OpCode::EOR, AddrMode::Absolute),
            0x51 => (OpCode::EOR, AddrMode::IndirectY),
            0x55 => (OpCode::EOR, AddrMode::ZeroPageX),
            0x59 => (OpCode::EOR, AddrMode::AbsoluteY),
            0x5D => (OpCode::EOR, AddrMode::AbsoluteX),
            // ADC
            0x61 => (OpCode::ADC, AddrMode::IndirectX),
            0x65 => (OpCode::ADC, AddrMode::ZeroPage),
            0x69 => (OpCode::ADC, AddrMode::Immediate),
            0x6D => (OpCode::ADC, AddrMode::Absolute),
            0x71 => (OpCode::ADC, AddrMode::IndirectY),
            0x75 => (OpCode::ADC, AddrMode::ZeroPageX),
            0x79 => (OpCode::ADC, AddrMode::AbsoluteY),
            0x7D => (OpCode::ADC, AddrMode::AbsoluteX),
            // STA
            0x81 => (OpCode::STA, AddrMode::IndirectX),
            0x85 => (OpCode::STA, AddrMode::ZeroPage),
            0x89 => (OpCode::NOP, AddrMode::Implicit),
            0x8D => (OpCode::STA, AddrMode::Absolute),
            0x91 => (OpCode::STA, AddrMode::IndirectY),
            0x95 => (OpCode::STA, AddrMode::ZeroPageX),
            0x99 => (OpCode::STA, AddrMode::AbsoluteY),
            0x9D => (OpCode::STA, AddrMode::AbsoluteX),
            // LDA
            0xA1 => (OpCode::LDA, AddrMode::IndirectX),
            0xA5 => (OpCode::LDA, AddrMode::ZeroPage),
            0xA9 => (OpCode::LDA, AddrMode::Immediate),
            0xAD => (OpCode::LDA, AddrMode::Absolute),
            0xB1 => (OpCode::LDA, AddrMode::IndirectY),
            0xB5 => (OpCode::LDA, AddrMode::ZeroPageX),
            0xB9 => (OpCode::LDA, AddrMode::AbsoluteY),
            0xBD => (OpCode::LDA, AddrMode::AbsoluteX),
            // CMP
            0xC1 => (OpCode::CMP, AddrMode::IndirectX),
            0xC5 => (OpCode::CMP, AddrMode::ZeroPage),
            0xC9 => (OpCode::CMP, AddrMode::Immediate),
            0xCD => (OpCode::CMP, AddrMode::Absolute),
            0xD1 => (OpCode::CMP, AddrMode::IndirectY),
            0xD5 => (OpCode::CMP, AddrMode::ZeroPageX),
            0xD9 => (OpCode::CMP, AddrMode::AbsoluteY),
            0xDD => (OpCode::CMP, AddrMode::AbsoluteX),
            // SBC
            0xE1 => (OpCode::SBC, AddrMode::IndirectX),
            0xE5 => (OpCode::SBC, AddrMode::ZeroPage),
            0xE9 | 0xEB => (OpCode::SBC, AddrMode::Immediate),
            0xED => (OpCode::SBC, AddrMode::Absolute),
            0xF1 => (OpCode::SBC, AddrMode::IndirectY),
            0xF5 => (OpCode::SBC, AddrMode::ZeroPageX),
            0xF9 => (OpCode::SBC, AddrMode::AbsoluteY),
            0xFD => (OpCode::SBC, AddrMode::AbsoluteX),
            // BRK
            0x00 => (OpCode::BRK, AddrMode::Implicit),
            // PHP
            0x08 => (OpCode::PHP, AddrMode::Implicit),
            // BPL
            0x10 => (OpCode::BPL, AddrMode::Relative),
            // CLC
            0x18 => (OpCode::CLC, AddrMode::Implicit),
            // JSR
            0x20 => (OpCode::JSR, AddrMode::Absolute),
            // BIT
            0x24 => (OpCode::BIT, AddrMode::ZeroPage),
            0x2C => (OpCode::BIT, AddrMode::Absolute),
            // PLP
            0x28 => (OpCode::PLP, AddrMode::Implicit),
            // BMI
            0x30 => (OpCode::BMI, AddrMode::Relative),
            // SEC
            0x38 => (OpCode::SEC, AddrMode::Implicit),
            // RTI
            0x40 => (OpCode::RTI, AddrMode::Implicit),
            // PHA
            0x48 => (OpCode::PHA, AddrMode::Implicit),
            // JMP
            0x4C => (OpCode::JMP, AddrMode::Absolute),
            0x6C => (OpCode::JMP, AddrMode::Indirect),
            // BVC
            0x50 => (OpCode::BVC, AddrMode::Relative),
            // CLI
            0x58 => (OpCode::CLI, AddrMode::Implicit),
            // RTS
            0x60 => (OpCode::RTS, AddrMode::Implicit),
            // PLA
            0x68 => (OpCode::PLA, AddrMode::Implicit),
            // BVS
            0x70 => (OpCode::BVS, AddrMode::Relative),
            // SEI
            0x78 => (OpCode::SEI, AddrMode::Implicit),
            // STY
            0x84 => (OpCode::STY, AddrMode::ZeroPage),
            0x8C => (OpCode::STY, AddrMode::Absolute),
            0x94 => (OpCode::STY, AddrMode::ZeroPageX),
            // DEY
            0x88 => (OpCode::DEY, AddrMode::Implicit),
            // BCC
            0x90 => (OpCode::BCC, AddrMode::Relative),
            // TYA
            0x98 => (OpCode::TYA, AddrMode::Implicit),
            // LDY
            0xA0 => (OpCode::LDY, AddrMode::Immediate),
            0xA4 => (OpCode::LDY, AddrMode::ZeroPage),
            0xAC => (OpCode::LDY, AddrMode::Absolute),
            0xB4 => (OpCode::LDY, AddrMode::ZeroPageX),
            0xBC => (OpCode::LDY, AddrMode::AbsoluteX),
            // TAY
            0xA8 => (OpCode::TAY, AddrMode::Implicit),
            // BCS
            0xB0 => (OpCode::BCS, AddrMode::Relative),
            // CLV
            0xB8 => (OpCode::CLV, AddrMode::Implicit),
            // CPY
            0xC0 => (OpCode::CPY, AddrMode::Immediate),
            0xC4 => (OpCode::CPY, AddrMode::ZeroPage),
            0xCC => (OpCode::CPY, AddrMode::Absolute),
            // INY
            0xC8 => (OpCode::INY, AddrMode::Implicit),
            // BNE
            0xD0 => (OpCode::BNE, AddrMode::Relative),
            // CLD
            0xD8 => (OpCode::CLD, AddrMode::Implicit),
            // CPX
            0xE0 => (OpCode::CPX, AddrMode::Immediate),
            0xE4 => (OpCode::CPX, AddrMode::ZeroPage),
            // INX
            0xE8 => (OpCode::INX, AddrMode::Implicit),
            // CPX
            0xEC => (OpCode::CPX, AddrMode::Absolute),
            // BEQ
            0xF0 => (OpCode::BEQ, AddrMode::Relative),
            // SED
            0xF8 => (OpCode::SED, AddrMode::Implicit),
            // ASL
            0x06 => (OpCode::ASL, AddrMode::ZeroPage),
            0x0A => (OpCode::ASL, AddrMode::Implicit),
            0x0E => (OpCode::ASL, AddrMode::Absolute),
            0x16 => (OpCode::ASL, AddrMode::ZeroPageX),
            0x1E => (OpCode::ASL, AddrMode::AbsoluteX),
            // ROL
            0x26 => (OpCode::ROL, AddrMode::ZeroPage),
            0x2A => (OpCode::ROL, AddrMode::Implicit),
            0x2E => (OpCode::ROL, AddrMode::Absolute),
            0x36 => (OpCode::ROL, AddrMode::ZeroPageX),
            0x3E => (OpCode::ROL, AddrMode::AbsoluteX),
            // LSR
            0x46 => (OpCode::LSR, AddrMode::ZeroPage),
            0x4A => (OpCode::LSR, AddrMode::Implicit),
            0x4E => (OpCode::LSR, AddrMode::Absolute),
            0x56 => (OpCode::LSR, AddrMode::ZeroPageX),
            0x5E => (OpCode::LSR, AddrMode::AbsoluteX),
            // ROR
            0x66 => (OpCode::ROR, AddrMode::ZeroPage),
            0x6A => (OpCode::ROR, AddrMode::Implicit),
            0x6E => (OpCode::ROR, AddrMode::Absolute),
            0x76 => (OpCode::ROR, AddrMode::ZeroPageX),
            0x7E => (OpCode::ROR, AddrMode::AbsoluteX),
            // STX
            0x86 => (OpCode::STX, AddrMode::ZeroPage),
            // TXA
            0x8A => (OpCode::TXA, AddrMode::Implicit),
            // STX
            0x8E => (OpCode::STX, AddrMode::Absolute),
            0x96 => (OpCode::STX, AddrMode::ZeroPageY),
            // TXS
            0x9A => (OpCode::TXS, AddrMode::Implicit),
            // LDX
            0xA2 => (OpCode::LDX, AddrMode::Immediate),
            0xA6 => (OpCode::LDX, AddrMode::ZeroPage),
            0xAE => (OpCode::LDX, AddrMode::Absolute),
            0xB6 => (OpCode::LDX, AddrMode::ZeroPageY),
            0xBE => (OpCode::LDX, AddrMode::AbsoluteY),
            // TAX
            0xAA => (OpCode::TAX, AddrMode::Implicit),
            // TSX
            0xBA => (OpCode::TSX, AddrMode::Implicit),
            // DEC
            0xC6 => (OpCode::DEC, AddrMode::ZeroPage),
            0xCE => (OpCode::DEC, AddrMode::Absolute),
            0xD6 => (OpCode::DEC, AddrMode::ZeroPageX),
            0xDE => (OpCode::DEC, AddrMode::AbsoluteX),
            // DEX
            0xCA => (OpCode::DEX, AddrMode::Implicit),
            // INC
            0xE6 => (OpCode::INC, AddrMode::ZeroPage),
            0xEE => (OpCode::INC, AddrMode::Absolute),
            0xF6 => (OpCode::INC, AddrMode::ZeroPageX),
            0xFE => (OpCode::INC, AddrMode::AbsoluteX),
            // NOP
            0xEA | 0x1A | 0x3A | 0x5A | 0x7A | 0xDA | 0xFA => (OpCode::NOP, AddrMode::Implicit),
            0x80 => (OpCode::NOP, AddrMode::Immediate),
            _ => panic!("Unknown opcode {:#x}", opcode_byte),
        }
    }

    fn parse_operand(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) -> Operand {
        match addr_mode {
            AddrMode::Implicit => {
                unreachable!(
                    "Parsing operand for {:?} addressing mode makes no sense!",
                    addr_mode
                )
            }
            AddrMode::Immediate => Operand::Memory(self.pc + 1),
            AddrMode::ZeroPage => Operand::Memory(self.read_mem(ctx, self.pc + 1) as u16),
            AddrMode::ZeroPageX => {
                Operand::Memory((self.read_mem(ctx, self.pc + 1) as u16 + self.x as u16) % 256)
            }
            AddrMode::ZeroPageY => {
                Operand::Memory((self.read_mem(ctx, self.pc + 1) as u16 + self.y as u16) % 256)
            }
            AddrMode::Absolute => Operand::Memory(u16::from_le_bytes([
                self.read_mem(ctx, self.pc + 1),
                self.read_mem(ctx, self.pc + 2),
            ])),
            AddrMode::AbsoluteX => Operand::Memory(
                u16::from_le_bytes([
                    self.read_mem(ctx, self.pc + 1),
                    self.read_mem(ctx, self.pc + 2),
                ]) + self.x as u16,
            ),
            AddrMode::AbsoluteY => Operand::Memory(
                u16::from_le_bytes([
                    self.read_mem(ctx, self.pc + 1),
                    self.read_mem(ctx, self.pc + 2),
                ]) + self.y as u16,
            ),
            AddrMode::Indirect => {
                let low_byte_pointer = u16::from_le_bytes([
                    self.read_mem(ctx, self.pc + 1),
                    self.read_mem(ctx, self.pc + 2),
                ]);
                let high_byte_pointer = if low_byte_pointer & 0b11111111 == 0xFF {
                    u16::from_le_bytes([0x00, self.read_mem(ctx, self.pc + 2)])
                } else {
                    low_byte_pointer + 1
                };
                Operand::Memory(u16::from_le_bytes([
                    self.read_mem(ctx, low_byte_pointer),
                    self.read_mem(ctx, high_byte_pointer),
                ]))
            }
            AddrMode::IndirectX => {
                let arg = self.read_mem(ctx, self.pc + 1) as u16;
                let x = self.x as u16;
                Operand::Memory(
                    (self.read_mem(ctx, (arg + x) % 256) as usize
                        + self.read_mem(ctx, (arg + x + 1) % 256) as usize * 256)
                        as u16,
                )
            }
            AddrMode::IndirectY => {
                let arg = self.read_mem(ctx, self.pc + 1) as u16;
                Operand::Memory(
                    self.read_mem(ctx, arg) as u16
                        + self.read_mem(ctx, (arg + 1) % 256) as u16 * 256
                        + self.y as u16,
                )
            }
            AddrMode::Relative => Operand::Offset(self.read_mem(ctx, self.pc + 1) as i8),
            _ => unimplemented!(
                "Operand parser for {:?} addressing mode is not implemented",
                addr_mode
            ),
        }
    }

    fn stack_push(&mut self, ctx: &mut CPUContext, value: u8) {
        let mem = &mut self.mem;
        let stack_top = STACK_BASE + self.s as u16;
        self.write_mem(ctx, stack_top, value);

        self.s = self.s.wrapping_sub(1);
    }

    fn stack_pop(&mut self, ctx: &mut CPUContext) -> u8 {
        self.s = self.s.wrapping_add(1);

        let stack_top = STACK_BASE + self.s as u16;
        let value = self.read_mem(ctx, stack_top);

        return value;
    }

    fn update_flags(&mut self, value: u8) {
        // Zero flag
        if value == 0 {
            self.set_zero_flag();
        } else {
            self.clear_zero_flag();
        }

        // Negative flag
        if value & 0b10000000 > 0 {
            self.set_negative_flag();
        } else {
            self.clear_negative_flag();
        }
    }

    pub fn do_interrupt(&mut self, ctx: &mut CPUContext) {
        let [ret_lsb, ret_msb] = (self.pc + 2).to_le_bytes();
        self.stack_push(ctx, ret_msb);
        self.stack_push(ctx, ret_lsb);

        self.stack_push(ctx, self.p | 0b00110000);

        self.set_interrupt_disable_flag();

        self.pc = u16::from_le_bytes([self.read_mem(ctx, 0xFFFE), self.read_mem(ctx, 0xFFFF)])
    }

    fn do_ora(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "ORA";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.a |= value;
        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_and(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "AND";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.a &= value;
        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_eor(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "EOR";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.a ^= value;
        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_adc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "ADC";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let old_a = self.a;
        let mut need_to_set_carry = false;
        self.a = self.a.wrapping_add(value);
        if self.a < old_a {
            need_to_set_carry = true;
        }
        if self.get_carry_flag() {
            let old_a = self.a;
            self.a = self.a.wrapping_add(1);

            if self.a < old_a {
                need_to_set_carry = true;
            }
        }
        if need_to_set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        if (old_a & 0x80 == value & 0x80) && (old_a & 0x80 != self.a & 0x80) {
            self.set_overflow_flag();
        } else {
            self.clear_overflow_flag();
        }

        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_sta(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "STA";

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_execute!(opcode_name);
        trace_register!(opcode_name, self.a);

        self.write_mem(ctx, address, self.a);
    }

    fn do_lda(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "LDA";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.a = value;
        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_cmp(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CMP";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        if self.a >= value {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        if self.a == value {
            self.set_zero_flag();
        } else {
            self.clear_zero_flag();
        }

        if self.a.wrapping_sub(value) & 0b10000000 > 0 {
            self.set_negative_flag()
        } else {
            self.clear_negative_flag()
        }

        trace_flags!(opcode_name, self.p);
    }

    fn do_sbc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "SBC";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX
                    | AddrMode::AbsoluteY
                    | AddrMode::IndirectX
                    | AddrMode::IndirectY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };
        let value = !value;

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let old_a = self.a;
        let mut need_to_set_carry = false;
        self.a = self.a.wrapping_add(value);
        if self.a < old_a {
            need_to_set_carry = true;
        }
        if self.get_carry_flag() {
            let old_a = self.a;
            self.a = self.a.wrapping_add(1);

            if self.a < old_a {
                need_to_set_carry = true;
            }
        }
        if need_to_set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        if (old_a & 0x80 == value & 0x80) && (old_a & 0x80 != self.a & 0x80) {
            self.set_overflow_flag();
        } else {
            self.clear_overflow_flag();
        }

        self.update_flags(self.a);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_php(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "PHP";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.stack_push(ctx, self.p | 0b00110000);

            trace_register!(opcode_name, self.s);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bpl(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BPL";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if !self.get_negative_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_clc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CLC";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.clear_carry_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_jsr(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "JSR";
        let target = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Absolute, &Operand::Memory(address)) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, target);
        trace_register!(opcode_name, self.pc);
        trace_register!(opcode_name, self.s);
        trace_execute!(opcode_name);

        let [ret_lsb, ret_msb] = (self.pc + 3 - 1).to_le_bytes();
        self.stack_push(ctx, ret_msb);
        self.stack_push(ctx, ret_lsb);
        self.pc = target;

        trace_register!(opcode_name, self.pc);
        trace_register!(opcode_name, self.s);
    }

    fn do_bit(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BIT";
        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::ZeroPage | AddrMode::Absolute, &Operand::Memory(address)) => {
                    self.read_mem(ctx, address)
                }
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        if self.a & value == 0 {
            self.set_zero_flag();
        } else {
            self.clear_zero_flag();
        }

        if value & 0b01000000 > 0 {
            self.set_overflow_flag();
        } else {
            self.clear_overflow_flag();
        }

        if value & 0b10000000 > 0 {
            self.set_negative_flag();
        } else {
            self.clear_negative_flag();
        }

        trace_flags!(opcode_name, self.p);
    }

    fn do_plp(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "PLP";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.p = self.stack_pop(ctx);

            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);

            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bmi(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BMI";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if self.get_negative_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_sec(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "SEC";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.set_carry_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_rti(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "RTI";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.p = self.stack_pop(ctx);
            self.pc = u16::from_le_bytes([self.stack_pop(ctx), self.stack_pop(ctx)]);

            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_pha(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "PHA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            trace_execute!(opcode_name);

            self.stack_push(ctx, self.a);

            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_jmp(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        // An original 6502 has does not correctly fetch the target address
        // if the indirect vector falls on a page boundary (e.g. $xxFF where
        // xx is any value from $00 to $FF). In this case fetches the LSB
        // from $xxFF as expected but takes the MSB from $xx00.
        let opcode_name = "JMP";
        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Absolute | AddrMode::Indirect, &Operand::Memory(address)) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.pc);
        trace_execute!(opcode_name);

        self.pc = address;

        trace_register!(opcode_name, self.pc);
    }

    fn do_bvc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BVC";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if !self.get_overflow_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_cli(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CLI";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.clear_interrupt_disable_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_rts(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "RTS";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            trace_execute!(opcode_name);

            let [lsb, msb] = [self.stack_pop(ctx), self.stack_pop(ctx)];
            self.pc = u16::from_le_bytes([lsb, msb]) + 1;

            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_pla(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "PLA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.a = self.stack_pop(ctx);
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bvs(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BVS";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if self.get_overflow_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
    }

    fn do_sei(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "SEI";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.set_interrupt_disable_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_sty(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "STY";
        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.y);
        trace_execute!(opcode_name);

        self.write_mem(ctx, address, self.y);
    }

    fn do_dey(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "DEY";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.y = self.y.wrapping_sub(1);
            self.update_flags(self.y);

            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bcc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BCC";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if !self.get_carry_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_tya(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TYA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.a = self.y;
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_ldy(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "LDY";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.y);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.y = value;
        self.update_flags(self.y);

        trace_register!(opcode_name, self.y);
        trace_flags!(opcode_name, self.p);
    }

    fn do_tay(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TAY";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.y);
            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.y = self.a;
            self.update_flags(self.y);

            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bcs(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BCS";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if self.get_carry_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_clv(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CLV";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.clear_overflow_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_cpy(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CPY";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate | AddrMode::ZeroPage | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.y);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        if self.y >= value {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        if self.y == value {
            self.set_zero_flag();
        } else {
            self.clear_zero_flag();
        }

        if self.y.wrapping_sub(value) & 0b10000000 > 1 {
            self.set_negative_flag();
        } else {
            self.clear_negative_flag();
        }

        trace_flags!(opcode_name, self.p);
    }

    fn do_iny(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "INY";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.y = self.y.wrapping_add(1);
            self.update_flags(self.y);

            trace_register!(opcode_name, self.y);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bne(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BNE";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_flags!(opcode_name, self.p);
        trace_register!(opcode_name, self.pc);
        trace_execute!(opcode_name);

        self.pc += 2;
        if !self.get_zero_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_flags!(opcode_name, self.p);
        trace_register!(opcode_name, self.pc);
    }

    fn do_cld(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "CLD";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.clear_decimal_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_cpx(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "CPX";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate | AddrMode::ZeroPage | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.x);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        if self.x >= value {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }

        if self.x == value {
            self.set_zero_flag();
        } else {
            self.clear_zero_flag();
        }

        if self.x.wrapping_sub(value) & 0b10000000 > 1 {
            self.set_negative_flag();
        } else {
            self.clear_negative_flag();
        }

        trace_register!(opcode_name, self.x);
        trace_flags!(opcode_name, self.p);
    }

    fn do_inx(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "INX";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.x);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.x = self.x.wrapping_add(1);
            self.update_flags(self.x);

            trace_register!(opcode_name, self.x);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_beq(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "BEQ";

        let offset = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (AddrMode::Relative, &Operand::Offset(offset)) => offset,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, offset);
        trace_register!(opcode_name, self.pc);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.pc += 2;
        if self.get_zero_flag() {
            self.pc = (self.pc as i32 + offset as i32) as u16;
        }

        trace_register!(opcode_name, self.pc);
    }

    fn do_sed(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "SED";

        if let AddrMode::Implicit = addr_mode {
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.set_decimal_flag();

            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_asl(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "ASL";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            if self.a & 0b10000000 > 1 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }

            self.a <<= 1;

            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            return;
        };

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let new_value;
        {
            let value = self.read_mem(ctx, address);
            if value & 0b10000000 > 1 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }
            new_value = value << 1;
            self.update_flags(new_value);
        }
        self.write_mem(ctx, address, new_value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_rol(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "ROL";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            let old_carry = self.get_carry_flag();
            if self.a & 0b10000000 > 1 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }
            self.a <<= 1;
            if old_carry {
                self.a |= 0b1;
            }
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            return;
        };

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let old_carry = self.get_carry_flag();
        let set_carry;

        let value = self.read_mem(ctx, address);
        set_carry = value & 0b10000000 > 1;
        self.write_mem(ctx, address, value << 1);
        let value = self.read_mem(ctx, address);
        if old_carry {
            self.write_mem(ctx, address, value | 0b1);
        }
        let value = self.read_mem(ctx, address);

        if set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_lsr(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "LSR";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            if self.a & 0b00000001 > 0 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }
            self.a >>= 1;
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            return;
        };

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let mut set_carry = false;

        let value = self.read_mem(ctx, address);
        if value & 0b00000001 > 0 {
            set_carry = true
        }
        self.write_mem(ctx, address, value >> 1);
        let value = self.read_mem(ctx, address);

        if set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_ror(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "ROR";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            let old_carry = self.get_carry_flag();
            if self.a & 0b00000001 > 0 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }
            self.a >>= 1;
            if old_carry {
                self.a |= 0b10000000;
            }
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            trace_flags!(opcode_name, self.p);
            return;
        };

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let old_carry = self.get_carry_flag();
        let mut set_carry;

        let value = self.read_mem(ctx, address);
        set_carry = value & 0b00000001 > 0;
        self.write_mem(ctx, address, value >> 1);
        let value = self.read_mem(ctx, address);
        if old_carry {
            self.write_mem(ctx, address, value | 0b10000000);
        }
        let value = self.read_mem(ctx, address);

        if set_carry {
            self.set_carry_flag()
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_stx(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "STX";

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::ZeroPage | AddrMode::ZeroPageY | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_register!(opcode_name, self.x);
        trace_execute!(opcode_name);

        self.write_mem(ctx, address, self.x);
    }

    fn do_txa(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TXA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.x);
            trace_execute!(opcode_name);

            self.a = self.x;
            self.update_flags(self.a);

            trace_register!(opcode_name, self.a);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_txs(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TXS";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.x);
            trace_execute!(opcode_name);

            self.s = self.x;

            trace_register!(opcode_name, self.s);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_ldx(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "LDX";

        let value = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageY
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteY,
                    &Operand::Memory(address),
                ) => self.read_mem(ctx, address),
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, value);
        trace_register!(opcode_name, self.x);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        self.x = value;
        self.update_flags(self.x);

        trace_register!(opcode_name, self.x);
        trace_flags!(opcode_name, self.p);
    }

    fn do_tax(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TAX";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.x);
            trace_register!(opcode_name, self.a);
            trace_execute!(opcode_name);

            self.x = self.a;
            self.update_flags(self.x);

            trace_register!(opcode_name, self.x);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_tsx(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "TSX";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.x);
            trace_register!(opcode_name, self.s);
            trace_execute!(opcode_name);

            self.x = self.s;
            self.update_flags(self.x);

            trace_register!(opcode_name, self.x);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_dec(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "DEC";

        let address = {
            let operand = self.parse_operand(ctx, addr_mode);
            trace_operand!(opcode_name, operand);
            match (addr_mode, &operand) {
                (
                    AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => address,
                _ => unimplemented!(
                    "Addressing mode {:?} (operand {:?}) is not implemented for {:?} opcode",
                    addr_mode,
                    operand,
                    opcode_name
                ),
            }
        };

        trace_operand_value!(opcode_name, address);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let new_value = self.read_mem(ctx, address).wrapping_sub(1);
        self.write_mem(ctx, address, new_value);

        self.update_flags(new_value);

        trace_flags!(opcode_name, self.p);
    }

    fn do_dex(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "DEX";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.x);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.x = self.x.wrapping_sub(1);
            self.update_flags(self.x);

            trace_register!(opcode_name, self.x);
            trace_flags!(opcode_name, self.p);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_inc(&mut self, ctx: &mut CPUContext, addr_mode: &AddrMode) {
        let opcode_name = "INC";
        let address = match addr_mode {
            AddrMode::Absolute | AddrMode::AbsoluteX | AddrMode::ZeroPage | AddrMode::ZeroPageX => {
                let operand = self.parse_operand(ctx, addr_mode);
                trace_operand!(opcode_name, operand);
                match operand {
                    Operand::Memory(address) => address,
                    _ => unreachable!(
                        "Operand {:?} is not defined for opcode {:?} with {:?} addressing mode",
                        operand, opcode_name, addr_mode
                    ),
                }
            }
            AddrMode::Implicit
            | AddrMode::Immediate
            | AddrMode::Relative
            | AddrMode::AbsoluteY
            | AddrMode::Indirect
            | AddrMode::IndirectX
            | AddrMode::IndirectY
            | AddrMode::ZeroPageY => unreachable!(
                "Addressing mode {:?} is not defined for {:?} opcode",
                addr_mode, opcode_name
            ),
            _ => unimplemented!(
                "Addressing mode {:?} is not implemented for {:?} opcode",
                addr_mode,
                opcode_name
            ),
        };

        trace_operand_value!(opcode_name, address);
        trace_flags!(opcode_name, self.p);
        trace_execute!(opcode_name);

        let new_value = self.read_mem(ctx, address).wrapping_add(1);
        self.write_mem(ctx, address, new_value);

        self.update_flags(new_value);

        trace_flags!(opcode_name, self.p);
    }

    fn do_nop(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "NOP";
        trace_execute!(opcode_name);
        // Literally do nothing
    }
}
