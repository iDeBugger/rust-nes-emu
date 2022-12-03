use crate::{
    cartridge::Cartridge,
    platform::{apu::APU, ppu::PPURegisters},
};

pub struct CPUContext<'ppu, 'apu, 'cartridge> {
    pub ppu_registers: &'ppu mut PPURegisters,
    pub apu: &'apu mut APU,
    pub cartidge: &'cartridge mut Cartridge,
}
