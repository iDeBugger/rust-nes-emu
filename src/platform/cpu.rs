use std::{cell::RefCell, rc::Rc};

use super::memory::Memory;

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

#[derive(Debug)]
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
    Value(u8),
    Memory(u16),
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

impl CPU {
    pub fn new(mem: Rc<RefCell<Memory>>) -> Self {
        CPU {
            a: 0x0,
            x: 0x0,
            y: 0x0,
            pc: 0xFFFC,
            s: 0x0,
            p: 0x0,
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

        self.run();
    }

    pub fn run(&mut self) {
        loop {
            let (opcode, addr_mode) = self.parse_operator();
            match opcode {
                OpCode::LDA => self.do_lda(&addr_mode),
                OpCode::STA => self.do_sta(&addr_mode),
                OpCode::ADC => self.do_adc(&addr_mode),
                OpCode::INC => self.do_inc(&addr_mode),
                OpCode::LDY => self.do_ldy(&addr_mode),
                OpCode::INY => self.do_iny(&addr_mode),
                OpCode::BRK => break,
                _ => unimplemented!("Opcode {:?} is not implemented", opcode),
            }

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
    }

    pub fn get_carry_flag(&self) -> bool {
        self.s & 0b00000001 > 0
    }

    fn set_carry_flag(&mut self) {
        self.s = self.s | 0b00000001
    }

    pub fn get_zero_flag(&self) -> bool {
        self.s & 0b00000010 > 0
    }

    pub fn get_overflow_flag(&self) -> bool {
        self.s & 0b01000000 > 0
    }

    fn set_overflow_flag(&mut self) {
        self.s = self.s | 0b01000000
    }

    pub fn get_negative_flag(&self) -> bool {
        self.s & 0b10000000 > 0
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
            0xE9 => (OpCode::SBC, AddrMode::Immediate),
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
            0xEA => (OpCode::NOP, AddrMode::Implicit),
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
            AddrMode::Immediate => Operand::Value(mem[self.pc as usize + 1]),
            AddrMode::ZeroPage => Operand::Memory(mem[self.pc as usize + 1] as u16),
            _ => unimplemented!(
                "Operand parser for {:?} addressing mode is not implemented",
                addr_mode
            ),
        }
    }

    fn update_flags(&mut self, value: u8) {
        // Zero flag
        if value == 0 {
            self.s = self.s | 0b10;
        } else {
            self.s = self.s & 0b11111101;
        }

        // Negative flag
        self.s = self.s | (value & 0b10000000)
    }

    fn do_lda(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "LDA";
        match addr_mode {
            AddrMode::Immediate => {
                let operand = self.parse_operand(&addr_mode);
                match operand {
                    Operand::Value(value) => {
                        self.a = value;
                        self.update_flags(value);
                    }
                    _ => unreachable!(
                        "Operand {:?} is not defined for opcode {:?} with {:?} addressing mode",
                        operand, opcode_name, addr_mode
                    ),
                }
            }
            AddrMode::Implicit | AddrMode::ZeroPageY | AddrMode::Indirect | AddrMode::Relative => {
                unreachable!(
                    "Addressing mode {:?} is not defined for {:?} opcode",
                    addr_mode, opcode_name
                )
            }
            _ => unimplemented!(
                "Addressing mode {:?} is not implemented for {:?} opcode",
                addr_mode,
                opcode_name
            ),
        }
    }

    fn do_sta(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "STA";
        match addr_mode {
            AddrMode::ZeroPage => {
                let operand = self.parse_operand(addr_mode);
                match operand {
                    Operand::Memory(address) => {
                        self.mem.borrow_mut()[address as usize] = self.a;
                    }
                    _ => unreachable!(
                        "Operand {:?} is not defined for opcode {:?} with {:?} addressing mode",
                        operand, opcode_name, addr_mode
                    ),
                }
            }
            AddrMode::Implicit
            | AddrMode::Immediate
            | AddrMode::Relative
            | AddrMode::Indirect
            | AddrMode::ZeroPageY => unreachable!(
                "Addressing mode {:?} is not defined for {:?} opcode",
                addr_mode, opcode_name
            ),
            _ => unimplemented!(
                "Addressing mode {:?} is not implemented for {:?} opcode",
                addr_mode,
                opcode_name
            ),
        }
    }

    fn do_adc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "ADC";
        match addr_mode {
            AddrMode::ZeroPage => {
                let operand = self.parse_operand(addr_mode);
                match operand {
                    Operand::Memory(address) => {
                        let value = self.mem.borrow()[address as usize];

                        let old_a = self.a;
                        self.a = self.a.wrapping_add(value);

                        if self.a < old_a {
                            self.set_carry_flag();
                        }

                        if self.get_carry_flag() {
                            let old_a = self.a;
                            self.a = self.a.wrapping_add(1);

                            if self.a < old_a {
                                self.set_carry_flag();
                            }
                        }

                        if (old_a & 0x80 == value & 0x80) && (old_a & 0x80 != self.a & 0x80) {
                            self.set_overflow_flag();
                        }
                    }
                    _ => unreachable!(
                        "Operand {:?} is not defined for opcode {:?} with {:?} addressing mode",
                        operand, opcode_name, addr_mode
                    ),
                }
            }
            AddrMode::Implicit | AddrMode::Relative | AddrMode::Indirect | AddrMode::ZeroPageY => {
                unreachable!(
                    "Addressing mode {:?} is not defined for {:?} opcode",
                    addr_mode, opcode_name
                )
            }
            _ => unimplemented!(
                "Addressing mode {:?} is not implemented for {:?} opcode",
                addr_mode,
                opcode_name
            ),
        }
    }

    fn do_inc(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "INC";
        match addr_mode {
            AddrMode::ZeroPage => {
                let operand = self.parse_operand(addr_mode);
                match operand {
                    Operand::Memory(address) => {
                        {
                            let mut mem = self.mem.borrow_mut();
                            mem[address as usize] += 1;
                        }

                        let new_value = self.mem.borrow()[address as usize];
                        self.update_flags(new_value)
                    }
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
        }
    }

    fn do_ldy(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "LDY";
        match addr_mode {
            AddrMode::ZeroPage => {
                let operand = self.parse_operand(&addr_mode);
                match operand {
                    Operand::Memory(address) => {
                        {
                            let mem = self.mem.borrow();
                            self.y = mem[address as usize];
                        }
                        self.update_flags(self.y);
                    }
                    _ => unreachable!(
                        "Operand {:?} is not defined for opcode {:?} with {:?} addressing mode",
                        operand, opcode_name, addr_mode
                    ),
                }
            }
            AddrMode::Implicit
            | AddrMode::Relative
            | AddrMode::AbsoluteY
            | AddrMode::Indirect
            | AddrMode::IndirectX
            | AddrMode::IndirectY
            | AddrMode::ZeroPageY => {
                unreachable!(
                    "Addressing mode {:?} is not defined for {:?} opcode",
                    addr_mode, opcode_name
                )
            }
            _ => unimplemented!(
                "Addressing mode {:?} is not implemented for {:?} opcode",
                addr_mode,
                opcode_name
            ),
        }
    }

    fn do_iny(&mut self, addr_mode: &AddrMode) {
        let opcode_name = "INY";
        match addr_mode {
            AddrMode::Implicit => {
                self.y += 1;
                self.update_flags(self.y);
            }
            _ => {
                unreachable!(
                    "Addressing mode {:?} is not defined for {:?} opcode",
                    addr_mode, opcode_name
                )
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::CPU;
    use std::{cell::RefCell, rc::Rc};

    #[test]
    fn test_simple_program() {
        let mem = Rc::new(RefCell::new([0u8; 65535]));
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
        let mem = Rc::new(RefCell::new([0u8; 65535]));
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
        let mem = Rc::new(RefCell::new([0u8; 65535]));
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
