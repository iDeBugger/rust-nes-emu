use std::ops::{Index, IndexMut};

const BASE_MEM: u16 = 0x4020;

pub struct CartridgeMemory {
    memory: [u8; 0xBFE0],
}

impl CartridgeMemory {
    pub fn new() -> Self {
        CartridgeMemory {
            memory: [0; 0xBFE0],
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x4020..=0xFFFF => &self.memory[address as usize - BASE_MEM as usize],
            _ => unreachable!("Cartridge memory can't address {}", address),
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x4020..=0xFFFF => &mut self.memory[address as usize - BASE_MEM as usize],
            _ => unreachable!("Cartridge memory can't address {}", address),
        }
    }
}

impl Index<u16> for CartridgeMemory {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        self.get_cell(index)
    }
}

impl IndexMut<u16> for CartridgeMemory {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        self.get_cell_mut(index)
    }
}
