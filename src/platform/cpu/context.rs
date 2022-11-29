use crate::platform::ppu::PPURegisters;

pub struct CPUContext<'ppu> {
    pub ppu_registers: &'ppu mut PPURegisters,
}
