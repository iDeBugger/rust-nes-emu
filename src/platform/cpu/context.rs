use crate::{cartridge::Cartridge, platform::ppu::PPURegisters};

pub struct CPUContext<'ppu, 'cartridge> {
    pub ppu_registers: &'ppu mut PPURegisters,
    pub cartidge: &'cartridge mut Cartridge,
}
