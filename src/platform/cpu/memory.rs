use super::CPUContext;

pub struct CPUMemory {
    ram: [u8; 0x0800],
}

impl CPUMemory {
    pub fn new() -> Self {
        CPUMemory { ram: [0u8; 0x0800] }
    }

    pub fn read(&self, ctx: &CPUContext, address: u16) -> u8 {
        match address {
            0x0000..=0x07FF => self.ram[address as usize],
            0x0800..=0x1FFF => self.ram[(address as usize) % self.ram.len()],
            0x2000..=0x3FFF => self.read_ppu_register(ctx, address),
            0x4000..=0x4013 => 0,
            0x4014 => ctx.ppu_registers.read_oamdma(),
            0x4015..=0x401F => 0,
            0x4020..=0xFFFF => ctx.cartidge.read_cpu_mem(address),
        }
    }

    fn read_ppu_register(&self, ctx: &CPUContext, address: u16) -> u8 {
        let register_number = (address - 0x2000) % 8;
        match register_number {
            0 => ctx.ppu_registers.read_ppuctrl(),
            1 => ctx.ppu_registers.read_ppumask(),
            2 => ctx.ppu_registers.read_ppustatus(),
            3 => ctx.ppu_registers.read_oamaddr(),
            4 => ctx.ppu_registers.read_oamdata(),
            5 => ctx.ppu_registers.read_ppuscroll(),
            6 => ctx.ppu_registers.read_ppuaddr(),
            7 => ctx.ppu_registers.read_ppudata(),
            _ => unreachable!(),
        }
    }

    pub fn write(&mut self, ctx: &mut CPUContext, address: u16, value: u8) {
        match address {
            0x0000..=0x07FF => self.ram[address as usize] = value,
            0x0800..=0x1FFF => self.ram[(address as usize) % self.ram.len()] = value,
            0x2000..=0x3FFF => self.write_ppu_register(ctx, address, value),
            0x4000..=0x4013 => {}
            0x4014 => ctx.ppu_registers.write_oamdma(value),
            0x4015..=0x401F => {}
            0x4020..=0xFFFF => ctx.cartidge.write_cpu_mem(address, value),
        }
    }

    fn write_ppu_register(&mut self, ctx: &mut CPUContext, address: u16, data: u8) {
        let register_number = (address - 0x2000) % 8;
        match register_number {
            0 => ctx.ppu_registers.write_ppuctrl(data),
            1 => ctx.ppu_registers.write_ppumask(data),
            2 => ctx.ppu_registers.write_ppustatus(data),
            3 => ctx.ppu_registers.write_oamaddr(data),
            4 => ctx.ppu_registers.write_oamdata(data),
            5 => ctx.ppu_registers.write_ppuscroll(data),
            6 => ctx.ppu_registers.write_ppuaddr(data),
            7 => ctx.ppu_registers.write_ppudata(data),
            _ => unreachable!(),
        }
    }
}
