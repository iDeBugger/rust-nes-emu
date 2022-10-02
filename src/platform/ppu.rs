use std::{cell::RefCell, rc::Rc};

use super::memory::Memory;

const PPUSTATUS: u16 = 0x2002;

pub struct PPU {
    mem: Rc<RefCell<Memory>>,
    scanline: u16,
    cycle: u16,
}

impl PPU {
    pub fn new(mem: Rc<RefCell<Memory>>) -> Self {
        let mut ppu = PPU {
            mem,
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
        let mut mem = self.mem.borrow_mut();
        mem[PPUSTATUS] |= 0b10000000;
    }

    fn clear_vbl_flag(&mut self) {
        let mut mem = self.mem.borrow_mut();
        mem[PPUSTATUS] &= 0b01111111;
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
