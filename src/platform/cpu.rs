use std::{
    cell::RefCell,
    ops::{Add, AddAssign},
    rc::Rc,
};

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
    Accumulator,
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
    LDA,
    STA,
    ADC,
    INC,
    LDY,
    INY,
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
                AddrMode::Accumulator => 1,
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
            0x00 => (OpCode::BRK, AddrMode::Implicit),
            0xa9 => (OpCode::LDA, AddrMode::Immediate),
            0x85 => (OpCode::STA, AddrMode::ZeroPage),
            0x65 => (OpCode::ADC, AddrMode::ZeroPage),
            0xe6 => (OpCode::INC, AddrMode::ZeroPage),
            0xa4 => (OpCode::LDY, AddrMode::ZeroPage),
            0xc8 => (OpCode::INY, AddrMode::Implicit),
            _ => panic!("Unknown opcode {:#x}", opcode_byte),
        }
    }

    fn parse_operand(&mut self, addr_mode: &AddrMode) -> Operand {
        let mem = self.mem.borrow();
        match addr_mode {
            AddrMode::Implicit | AddrMode::Accumulator => {
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
            AddrMode::Implicit
            | AddrMode::ZeroPageY
            | AddrMode::Accumulator
            | AddrMode::Indirect
            | AddrMode::Relative => {
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
            | AddrMode::Accumulator
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
            AddrMode::Implicit
            | AddrMode::Accumulator
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
            | AddrMode::Accumulator
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
            | AddrMode::Accumulator
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
