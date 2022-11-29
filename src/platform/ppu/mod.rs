mod registers;

pub use self::registers::PPURegisters;

pub struct PPU {
    pub registers: PPURegisters,
    scanline: u16,
    cycle: u16,
}

impl PPU {
    pub fn new() -> Self {
        let mut ppu = PPU {
            registers: PPURegisters::new(),
            scanline: 0,
            cycle: 0,
        };
        ppu.set_vbl_flag();
        ppu
    }

    pub fn run_step(&mut self) {
        match self.scanline {
            0..=239 => self.process_visible_scanline(),
            240 => self.process_post_render_scanline(),
            241..=260 => self.process_vertical_blanking_lines(),
            261 => self.process_prerender_scanline(),
            _ => unreachable!(),
        }

        self.cycle = (self.cycle + 1) % 341;
        if self.cycle == 0 {
            self.scanline = (self.scanline + 1) % 262;
        }
    }

    fn set_vbl_flag(&mut self) {
        let ppustatus = self.registers.read_ppustatus();
        self.registers.write_ppustatus(ppustatus | 0b10000000);
    }

    fn clear_vbl_flag(&mut self) {
        let ppustatus = self.registers.read_ppustatus();
        self.registers.write_ppustatus(ppustatus & 0b01111111);
    }

    fn process_visible_scanline(&mut self) {}

    fn process_post_render_scanline(&mut self) {}

    fn process_vertical_blanking_lines(&mut self) {
        if self.scanline == 241 && self.cycle == 1 {
            self.set_vbl_flag();
        }
    }

    fn process_prerender_scanline(&mut self) {
        if self.cycle == 1 {
            self.clear_vbl_flag();
        }
    }
}
