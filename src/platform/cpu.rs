use super::memory::Memory;
use log::{debug, trace, warn};
use std::{cell::RefCell, rc::Rc};

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

#[derive(Debug)]
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

#[derive(Debug, PartialEq, Eq)]
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
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub pc: u16,
    pub s: u8,
    pub p: u8,
    mem: Rc<RefCell<Memory>>,
}

const STACK_BASE: u16 = 0x0100;

impl CPU {
    pub fn new(mem: Rc<RefCell<Memory>>) -> Self {
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

    pub fn load_and_run(&mut self, place: u16, program: Vec<u8>) {
        self.pc = place;

        {
            let mut mem = self.mem.borrow_mut();
            let place = place as usize;
            for (program_index, program_cell) in program.iter().enumerate() {
                let mem_index = place + program_index;
                mem[mem_index] = *program_cell;
            }
        }

        loop {
            if self.run_step(true) {
                break;
            }
        }
    }

    pub fn run_step(&mut self, stop_at_loop: bool) -> bool {
        trace!("Running CPU step...");
        let old_pc = self.pc;

        let (opcode, addr_mode) = self.parse_operator();
        trace!(
            "Executing {:?} ({:?}) at {:#X?}",
            opcode,
            addr_mode,
            self.pc
        );
        match opcode {
            OpCode::ORA => self.do_ora(&addr_mode),
            OpCode::AND => self.do_and(&addr_mode),
            OpCode::EOR => self.do_eor(&addr_mode),
            OpCode::ADC => self.do_adc(&addr_mode),
            OpCode::STA => self.do_sta(&addr_mode),
            OpCode::LDA => self.do_lda(&addr_mode),
            OpCode::CMP => self.do_cmp(&addr_mode),
            OpCode::SBC => self.do_sbc(&addr_mode),

            OpCode::PHP => self.do_php(&addr_mode),
            OpCode::BPL => self.do_bpl(&addr_mode),
            OpCode::CLC => self.do_clc(&addr_mode),
            OpCode::JSR => self.do_jsr(&addr_mode),
            OpCode::BIT => self.do_bit(&addr_mode),
            OpCode::PLP => self.do_plp(&addr_mode),
            OpCode::BMI => self.do_bmi(&addr_mode),
            OpCode::SEC => self.do_sec(&addr_mode),
            OpCode::RTI => self.do_rti(&addr_mode),
            OpCode::PHA => self.do_pha(&addr_mode),
            OpCode::JMP => self.do_jmp(&addr_mode),
            OpCode::BVC => self.do_bvc(&addr_mode),
            OpCode::CLI => self.do_cli(&addr_mode),
            OpCode::RTS => self.do_rts(&addr_mode),
            OpCode::PLA => self.do_pla(&addr_mode),
            OpCode::BVS => self.do_bvs(&addr_mode),
            OpCode::SEI => self.do_sei(&addr_mode),
            OpCode::STY => self.do_sty(&addr_mode),
            OpCode::DEY => self.do_dey(&addr_mode),
            OpCode::BCC => self.do_bcc(&addr_mode),
            OpCode::TYA => self.do_tya(&addr_mode),
            OpCode::LDY => self.do_ldy(&addr_mode),
            OpCode::TAY => self.do_tay(&addr_mode),
            OpCode::BCS => self.do_bcs(&addr_mode),
            OpCode::CLV => self.do_clv(&addr_mode),
            OpCode::CPY => self.do_cpy(&addr_mode),
            OpCode::INY => self.do_iny(&addr_mode),
            OpCode::BNE => self.do_bne(&addr_mode),
            OpCode::CLD => self.do_cld(&addr_mode),
            OpCode::CPX => self.do_cpx(&addr_mode),
            OpCode::INX => self.do_inx(&addr_mode),
            OpCode::BEQ => self.do_beq(&addr_mode),
            OpCode::SED => self.do_sed(&addr_mode),

            OpCode::ASL => self.do_asl(&addr_mode),
            OpCode::ROL => self.do_rol(&addr_mode),
            OpCode::LSR => self.do_lsr(&addr_mode),
            OpCode::ROR => self.do_ror(&addr_mode),
            OpCode::STX => self.do_stx(&addr_mode),
            OpCode::TXA => self.do_txa(&addr_mode),
            OpCode::TXS => self.do_txs(&addr_mode),
            OpCode::LDX => self.do_ldx(&addr_mode),
            OpCode::TAX => self.do_tax(&addr_mode),
            OpCode::TSX => self.do_tsx(&addr_mode),
            OpCode::DEC => self.do_dec(&addr_mode),
            OpCode::DEX => self.do_dex(&addr_mode),
            OpCode::INC => self.do_inc(&addr_mode),
            OpCode::NOP => self.do_nop(&addr_mode),
            OpCode::BRK => return true,
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

    fn parse_operator(&self) -> (OpCode, AddrMode) {
        let opcode_byte = self.mem.borrow()[self.pc as usize];
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

    fn parse_operand(&mut self, addr_mode: &AddrMode) -> Operand {
        let mem = self.mem.borrow();
        match addr_mode {
            AddrMode::Implicit => {
                unreachable!(
                    "Parsing operand for {:?} addressing mode makes no sense!",
                    addr_mode
                )
            }
            AddrMode::Immediate => Operand::Memory(self.pc + 1),
            AddrMode::ZeroPage => Operand::Memory(mem[self.pc as usize + 1] as u16),
            AddrMode::ZeroPageX => {
                Operand::Memory((mem[self.pc as usize + 1] as u16 + self.x as u16) % 256)
            }
            AddrMode::ZeroPageY => {
                Operand::Memory((mem[self.pc as usize + 1] as u16 + self.y as u16) % 256)
            }
            AddrMode::Absolute => Operand::Memory(u16::from_le_bytes([
                mem[self.pc as usize + 1],
                mem[self.pc as usize + 2],
            ])),
            AddrMode::AbsoluteX => Operand::Memory(
                u16::from_le_bytes([mem[self.pc as usize + 1], mem[self.pc as usize + 2]])
                    + self.x as u16,
            ),
            AddrMode::AbsoluteY => Operand::Memory(
                u16::from_le_bytes([mem[self.pc as usize + 1], mem[self.pc as usize + 2]])
                    + self.y as u16,
            ),
            AddrMode::Indirect => {
                let address_pointer =
                    u16::from_le_bytes([mem[self.pc as usize + 1], mem[self.pc as usize + 2]]);
                Operand::Memory(u16::from_le_bytes([
                    mem[address_pointer as usize],
                    mem[address_pointer as usize + 1],
                ]))
            }
            AddrMode::IndirectX => {
                let arg = mem[self.pc as usize + 1] as usize;
                let x = self.x as usize;
                Operand::Memory(
                    (mem[(arg + x) % 256] as usize + mem[(arg + x + 1) % 256] as usize * 256)
                        as u16,
                )
            }
            AddrMode::IndirectY => {
                let arg = mem[self.pc as usize + 1];
                Operand::Memory(
                    mem[arg as usize] as u16
                        + mem[(arg as usize + 1) % 256] as u16 * 256
                        + self.y as u16,
                )
            }
            AddrMode::Relative => Operand::Offset(mem[self.pc as usize + 1] as i8),
            _ => unimplemented!(
                "Operand parser for {:?} addressing mode is not implemented",
                addr_mode
            ),
        }
    }

    fn stack_push(&mut self, value: u8) {
        let mut mem = self.mem.borrow_mut();
        let stack_top = STACK_BASE + self.s as u16;
        mem[stack_top as usize] = value;

        self.s -= 1;
    }

    fn stack_pop(&mut self) -> u8 {
        self.s += 1;

        let mem = self.mem.borrow();
        let stack_top = STACK_BASE + self.s as u16;
        let value = mem[stack_top as usize];

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

    fn do_ora(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "ORA";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_and(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "AND";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_eor(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "EOR";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_adc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "ADC";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_sta(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "STA";

        let address = {
            let operand = self.parse_operand(addr_mode);
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

        let mut mem = self.mem.borrow_mut();
        mem[address as usize] = self.a;
    }

    fn do_lda(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "LDA";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_cmp(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "CMP";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_sbc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "SBC";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
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
                ) => mem[address as usize],
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

    fn do_php(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "PHP";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.stack_push(self.p | 0b00110000);

            trace_register!(opcode_name, self.s);
            return;
        };

        unimplemented!(
            "Addressing mode {:?} is not implemented for {:?} opcode",
            addr_mode,
            opcode_name
        )
    }

    fn do_bpl(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BPL";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_clc(&mut self, addr_mode: &AddrMode) {
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

    fn do_jsr(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "JSR";
        let target = {
            let operand = self.parse_operand(addr_mode);
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
        self.stack_push(ret_msb);
        self.stack_push(ret_lsb);
        self.pc = target;

        trace_register!(opcode_name, self.pc);
        trace_register!(opcode_name, self.s);
    }

    fn do_bit(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BIT";
        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
            match (addr_mode, &operand) {
                (AddrMode::ZeroPage | AddrMode::Absolute, &Operand::Memory(address)) => {
                    mem[address as usize]
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

    fn do_plp(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "PLP";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.p = self.stack_pop();

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

    fn do_bmi(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BMI";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_sec(&mut self, addr_mode: &AddrMode) {
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

    fn do_rti(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "RTI";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.p = self.stack_pop();
            self.pc = u16::from_le_bytes([self.stack_pop(), self.stack_pop()]);

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

    fn do_pha(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "PHA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            trace_execute!(opcode_name);

            self.stack_push(self.a);

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

    fn do_jmp(&mut self, addr_mode: &AddrMode) {
        // An original 6502 has does not correctly fetch the target address
        // if the indirect vector falls on a page boundary (e.g. $xxFF where
        // xx is any value from $00 to $FF). In this case fetches the LSB
        // from $xxFF as expected but takes the MSB from $xx00.
        let opcode_name = "JMP";
        let address = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_bvc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BVC";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_cli(&mut self, addr_mode: &AddrMode) {
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

    fn do_rts(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "RTS";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.s);
            trace_register!(opcode_name, self.pc);
            trace_execute!(opcode_name);

            let [lsb, msb] = [self.stack_pop(), self.stack_pop()];
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

    fn do_pla(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "PLA";

        if let AddrMode::Implicit = addr_mode {
            trace_register!(opcode_name, self.a);
            trace_register!(opcode_name, self.s);
            trace_flags!(opcode_name, self.p);
            trace_execute!(opcode_name);

            self.a = self.stack_pop();
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

    fn do_bvs(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BVS";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_sei(&mut self, addr_mode: &AddrMode) {
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

    fn do_sty(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "STY";
        let address = {
            let operand = self.parse_operand(addr_mode);
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

        let mut mem = self.mem.borrow_mut();
        mem[address as usize] = self.y;
    }

    fn do_dey(&mut self, addr_mode: &AddrMode) {
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

    fn do_bcc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BCC";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_tya(&mut self, addr_mode: &AddrMode) {
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

    fn do_ldy(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "LDY";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageX
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteX,
                    &Operand::Memory(address),
                ) => mem[address as usize],
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

    fn do_tay(&mut self, addr_mode: &AddrMode) {
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

    fn do_bcs(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BCS";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_clv(&mut self, addr_mode: &AddrMode) {
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

    fn do_cpy(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "CPY";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate | AddrMode::ZeroPage | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => mem[address as usize],
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

    fn do_iny(&mut self, addr_mode: &AddrMode) {
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

    fn do_bne(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BNE";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_cpx(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "CPX";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate | AddrMode::ZeroPage | AddrMode::Absolute,
                    &Operand::Memory(address),
                ) => mem[address as usize],
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

    fn do_inx(&mut self, addr_mode: &AddrMode) {
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

    fn do_beq(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "BEQ";

        let offset = {
            let operand = self.parse_operand(addr_mode);
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

    fn do_sed(&mut self, addr_mode: &AddrMode) {
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

    fn do_asl(&mut self, addr_mode: &AddrMode) {
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
            let operand = self.parse_operand(addr_mode);
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
            let value = self.mem.borrow_mut()[address as usize];
            if value & 0b10000000 > 1 {
                self.set_carry_flag();
            } else {
                self.clear_carry_flag();
            }
            new_value = value << 1;
            self.update_flags(new_value);
        }
        self.mem.borrow_mut()[address as usize] = new_value;

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_rol(&mut self, addr_mode: &AddrMode) {
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
            let operand = self.parse_operand(addr_mode);
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
        let new_value;
        {
            let value = &mut self.mem.borrow_mut()[address as usize];
            set_carry = *value & 0b10000000 > 1;
            *value <<= 1;
            if old_carry {
                *value |= 0b1;
            }
            new_value = *value;
        }
        if set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(new_value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_lsr(&mut self, addr_mode: &AddrMode) {
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
            let operand = self.parse_operand(addr_mode);
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
        let new_value;
        {
            let value = &mut self.mem.borrow_mut()[address as usize];
            if *value & 0b00000001 > 0 {
                set_carry = true
            }
            *value >>= 1;
            new_value = *value;
        }
        if set_carry {
            self.set_carry_flag();
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(new_value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_ror(&mut self, addr_mode: &AddrMode) {
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
            let operand = self.parse_operand(addr_mode);
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
        let new_value;
        {
            let value = &mut self.mem.borrow_mut()[address as usize];
            set_carry = *value & 0b00000001 > 0;
            *value >>= 1;
            if old_carry {
                *value |= 0b10000000;
            }
            new_value = *value;
        }
        if set_carry {
            self.set_carry_flag()
        } else {
            self.clear_carry_flag();
        }
        self.update_flags(new_value);

        trace_register!(opcode_name, self.a);
        trace_flags!(opcode_name, self.p);
    }

    fn do_stx(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "STX";

        let address = {
            let operand = self.parse_operand(addr_mode);
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

        let mut mem = self.mem.borrow_mut();
        mem[address as usize] = self.x;
    }

    fn do_txa(&mut self, addr_mode: &AddrMode) {
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

    fn do_txs(&mut self, addr_mode: &AddrMode) {
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

    fn do_ldx(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "LDX";

        let value = {
            let operand = self.parse_operand(addr_mode);
            trace_operand!(opcode_name, operand);
            let mem = self.mem.borrow();
            match (addr_mode, &operand) {
                (
                    AddrMode::Immediate
                    | AddrMode::ZeroPage
                    | AddrMode::ZeroPageY
                    | AddrMode::Absolute
                    | AddrMode::AbsoluteY,
                    &Operand::Memory(address),
                ) => mem[address as usize],
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

    fn do_tax(&mut self, addr_mode: &AddrMode) {
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

    fn do_tsx(&mut self, addr_mode: &AddrMode) {
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

    fn do_dec(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "DEC";

        let address = {
            let operand = self.parse_operand(addr_mode);
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

        let new_value;
        {
            let mut mem = self.mem.borrow_mut();
            mem[address as usize] = mem[address as usize].wrapping_sub(1);
            new_value = mem[address as usize];
        }
        self.update_flags(new_value);

        trace_flags!(opcode_name, self.p);
    }

    fn do_dex(&mut self, addr_mode: &AddrMode) {
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

    fn do_inc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "INC";
        let address = match addr_mode {
            AddrMode::ZeroPage | AddrMode::ZeroPageX => {
                let operand = self.parse_operand(addr_mode);
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

        {
            let mut mem = self.mem.borrow_mut();
            mem[address as usize] = mem[address as usize].wrapping_add(1);
        }
        let new_value = self.mem.borrow()[address as usize];
        self.update_flags(new_value);

        trace_flags!(opcode_name, self.p);
    }

    fn do_nop(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "NOP";
        trace_execute!(opcode_name);
        // Literally do nothing
    }
}

#[cfg(test)]
mod test {
    use crate::rom::INesFormat;

    use super::CPU;
    use std::{cell::RefCell, rc::Rc};

    #[test]
    fn test_simple_program() {
        let mem = Rc::new(RefCell::new([0u8; 65536]));
        let mut cpu = CPU::new(mem.clone());

        cpu.load_and_run(
            0x0100,
            vec![
                0xa9, 0x10, // LDA #$10     -> A = #$10
                0x85, 0x20, // STA $20      -> $20 = #$10
                0xa9, 0x01, // LDA #$1      -> A = #$1
                0x65, 0x20, // ADC $20      -> A = #$11
                0x85, 0x21, // STA $21      -> $21=#$11
                0xe6, 0x21, // INC $21      -> $21=#$12
                0xa4, 0x21, // LDY $21      -> Y=#$12
                0xc8, // INY          -> Y=#$13
                0x00, // BRK
            ],
        );

        let mem = mem.borrow();

        assert_eq!(mem[0x20], 0x10);
        assert_eq!(mem[0x21], 0x12);
        assert_eq!(cpu.a, 0x11);
        assert_eq!(cpu.y, 0x13);
    }

    #[test]
    fn test_simple_flags() {
        let mem = Rc::new(RefCell::new([0u8; 65536]));
        let mut cpu = CPU::new(mem.clone());

        cpu.load_and_run(
            0x0100,
            vec![
                0xa9, 0xff, // LDA #$ff
                0x85, 0x30, // STA $30 -> $30 = #$ff
                0xa9, 0x01, // LDA #$1
                0x65, 0x30, // ADC $30 -> carry, A = 0
                0xa9, 0x01, // LDA #$1
                0x65, 0x30, // ADC $30 -> carry, A = 1
                0x00, // BRK
            ],
        );

        assert_eq!(cpu.a, 0x1);
        assert_eq!(cpu.s & 0x1, 0x1);
    }

    #[test]
    fn test_lda_immediate_simple() {
        let mem = Rc::new(RefCell::new([0u8; 65536]));
        let mut cpu = CPU::new(mem.clone());

        cpu.load_and_run(
            0x0100,
            vec![
                0xa9, 0x10, // LDA #$10 -> A = #$10
                0x00, // BRK
            ],
        );

        assert_eq!(cpu.a, 0x10);
    }
}
