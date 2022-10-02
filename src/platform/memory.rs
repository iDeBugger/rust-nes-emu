use std::ops::{Index, IndexMut};

pub struct Memory {
    internal_ram: [u8; 0x0800],
    ppu_registers: [u8; 0x0008],
    apu_io_registers: [u8; 0x0018],
    apu_io_test_registers: [u8; 0x0008],
    cartridge_space: [u8; 0xBFE0],
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            internal_ram: [0; 0x0800],
            ppu_registers: [0; 0x0008],
            apu_io_registers: [0; 0x0018],
            apu_io_test_registers: [0; 0x0008],
            cartridge_space: [0; 0xBFE0],
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x0000..=0x07FF => &self.internal_ram[address as usize],
            0x0800..=0x1FFF => &self.internal_ram[address as usize % 0x0800],
            0x2000..=0x2007 => &self.ppu_registers[address as usize - 0x2000],
            0x2008..=0x3FFF => &self.ppu_registers[(address as usize - 0x2000) % 0x0008],
            0x4000..=0x4017 => &self.apu_io_registers[address as usize - 0x4000],
            0x4018..=0x401F => &0,
            0x4020..=0xFFFF => &self.cartridge_space[address as usize - 0x4020],
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x0000..=0x07FF => &mut self.internal_ram[address as usize],
            0x0800..=0x1FFF => &mut self.internal_ram[address as usize % 0x0800],
            0x2000..=0x2007 => &mut self.ppu_registers[address as usize - 0x2000],
            0x2008..=0x3FFF => &mut self.ppu_registers[(address as usize - 0x2000) % 0x0008],
            0x4000..=0x4017 => &mut self.apu_io_registers[address as usize - 0x4000],
            0x4018..=0x401F => &mut self.apu_io_test_registers[address as usize - 0x4018],
            0x4020..=0xFFFF => &mut self.cartridge_space[address as usize - 0x4020],
        }
    }
}

impl Index<u16> for Memory {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        self.get_cell(index)
    }
}

impl IndexMut<u16> for Memory {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        self.get_cell_mut(index)
    }
}
