use std::ops::{Index, IndexMut};

const BASE_MEM: u16 = 0x4000;

pub struct ApuIoMemory {
    memory: [u8; 0x0018],
    test_mode_memory: [u8; 0x0008],
}

impl ApuIoMemory {
    pub fn new() -> Self {
        ApuIoMemory {
            memory: [0; 0x0018],
            test_mode_memory: [0; 0x0008],
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x4000..=0x4017 => &self.memory[address as usize - BASE_MEM as usize],
            0x4018..=0x401F => &self.test_mode_memory[address as usize - BASE_MEM as usize],
            _ => unreachable!("APU and IO memory can't address {}", address),
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x4000..=0x4017 => &mut self.memory[address as usize - BASE_MEM as usize],
            0x4018..=0x401F => &mut self.test_mode_memory[address as usize - BASE_MEM as usize],
            _ => unreachable!("APU and IO memory can't address {}", address),
        }
    }
}

impl Index<u16> for ApuIoMemory {
    type Output = u8;

    fn index(&self, index: u16) -> &Self::Output {
        self.get_cell(index)
    }
}

impl IndexMut<u16> for ApuIoMemory {
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        self.get_cell_mut(index)
    }
}
