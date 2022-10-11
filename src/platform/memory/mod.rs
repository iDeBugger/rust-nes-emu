use std::ops::{Index, IndexMut};

use self::{
    apu_io_memory::ApuIoMemory, cartridge_memory::CartridgeMemory, cpu_memory::CpuMemory,
    ppu_memory::PpuMemory,
};

mod apu_io_memory;
mod cartridge_memory;
mod cpu_memory;
mod ppu_memory;

pub struct Memory {
    cpu_memory: CpuMemory,
    ppu_memory: PpuMemory,
    apu_io_memory: ApuIoMemory,
    cartridge_memory: CartridgeMemory,
}

impl Memory {
    pub fn new() -> Self {
        Memory {
            cpu_memory: CpuMemory::new(),
            ppu_memory: PpuMemory::new(),
            apu_io_memory: ApuIoMemory::new(),
            cartridge_memory: CartridgeMemory::new(),
        }
    }

    fn get_cell(&self, address: u16) -> &u8 {
        match address {
            0x0000..=0x1FFF => &self.cpu_memory[address],
            0x2000..=0x3FFF => &self.ppu_memory[address],
            0x4000..=0x401F => &self.apu_io_memory[address],
            0x4020..=0xFFFF => &self.cartridge_memory[address],
        }
    }

    fn get_cell_mut(&mut self, address: u16) -> &mut u8 {
        match address {
            0x0000..=0x1FFF => &mut self.cpu_memory[address],
            0x2000..=0x3FFF => &mut self.ppu_memory[address],
            0x4000..=0x401F => &mut self.apu_io_memory[address],
            0x4020..=0xFFFF => &mut self.cartridge_memory[address],
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
