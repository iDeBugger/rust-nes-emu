use std::ops::{Index, IndexMut};

const BASE_MEM: u16 = 0x2000;

pub struct PpuMemory {
    memory: [u8; 0x0008],
}

impl PpuMemory {
    pub fn new() -> Self {
        PpuMemory {
            memory: [0; 0x0008],
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x2000..=0x2007 => &self.memory[address as usize - BASE_MEM as usize],
            0x2008..=0x3FFF => {
                &self.memory[(address as usize - BASE_MEM as usize) % self.memory.len()]
            }
            _ => unreachable!("PPU memory can't address {}", address),
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x2000..=0x2007 => &mut self.memory[address as usize - BASE_MEM as usize],
            0x2008..=0x3FFF => {
                &mut self.memory[(address as usize - BASE_MEM as usize) % self.memory.len()]
            }
            _ => unreachable!("PPU memory can't address {}", address),
        }
    }
}

impl Index<u16> for PpuMemory {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        self.get_cell(index)
    }
}

impl IndexMut<u16> for PpuMemory {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        self.get_cell_mut(index)
    }
}
