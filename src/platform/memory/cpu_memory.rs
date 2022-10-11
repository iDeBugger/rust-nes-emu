use std::ops::{Index, IndexMut};

pub struct CpuMemory {
    memory: [u8; 0x0800],
}

impl CpuMemory {
    pub fn new() -> Self {
        CpuMemory {
            memory: [0; 0x0800],
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x0000..=0x07FF => &self.memory[address as usize],
            0x0800..=0x1FFF => &self.memory[(address as usize) % self.memory.len()],
            _ => unreachable!("CPU memory can't address {}", address),
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x0000..=0x07FF => &mut self.memory[address as usize],
            0x0800..=0x1FFF => &mut self.memory[(address as usize) % self.memory.len()],
            _ => unreachable!("CPU memory can't address {}", address),
        }
    }
}

impl Index<u16> for CpuMemory {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        self.get_cell(index)
    }
}

impl IndexMut<u16> for CpuMemory {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        self.get_cell_mut(index)
    }
}
