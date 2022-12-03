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
            0x4000..=0x4013 => self.read_apu_register(ctx, address),
            0x4014 => ctx.ppu_registers.read_oamdma(),
            0x4015..=0x4017 => self.read_apu_register(ctx, address),
            0x4018..=0x401F => 0,
            0x4020..=0xFFFF => ctx.cartidge.read_cpu_mem(address),
        }
    }

    fn read_apu_register(&self, ctx: &CPUContext, address: u16) -> u8 {
        match address {
            0x4015 => ctx.apu.read_status_register(),
            _ => unreachable!("APU register {:#04x} is not readable!", address),
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
            0x4000..=0x4013 => self.write_apu_register(ctx, address, value),
            0x4014 => ctx.ppu_registers.write_oamdma(value),
            0x4015 => ctx.apu.write_status_register(value),
            0x4016 => {}
            0x4017 => ctx.apu.write_frame_counter_register(value),
            0x4018..=0x401F => {}
            0x4020..=0xFFFF => ctx.cartidge.write_cpu_mem(address, value),
        }
    }

    fn write_apu_register(&mut self, ctx: &mut CPUContext, address: u16, value: u8) {
        match address {
            0x4000 => ctx.apu.write_pulse1_1(value),
            0x4001 => {}
            0x4002 => {}
            0x4003 => ctx.apu.write_pulse1_4(value),
            0x4004 => ctx.apu.write_pulse2_1(value),
            0x4005 => {}
            0x4006 => {}
            0x4007 => ctx.apu.write_pulse2_4(value),
            0x4008 => ctx.apu.write_triangle_1(value),
            0x4009 => {}
            0x400A => {}
            0x400B => ctx.apu.write_triangle_4(value),
            0x400C => ctx.apu.write_noise_1(value),
            0x400D => {}
            0x400E => {}
            0x400F => ctx.apu.write_noise_4(value),
            0x4010 => {}
            0x4011 => {}
            0x4012 => {}
            0x4013 => {}
            _ => unreachable!("APU register {:#04x} is not writeable!", address),
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
