use crate::cartridge::Cartridge;

use super::Mapper;

enum Mapper0Subtype {
    NRom128,
    NRom256,
}

pub struct Mapper0 {
    prg_rom_data: Vec<u8>,
    chr_rom_data: Vec<u8>,
    subtype: Mapper0Subtype,
    prg_ram: [u8; 0x2000],
}

impl Mapper0 {
    pub fn new(prg_rom_data: Vec<u8>, chr_rom_data: Vec<u8>) -> Self {
        let subtype = if prg_rom_data.len() > 0x4000 {
            Mapper0Subtype::NRom256
        } else {
            Mapper0Subtype::NRom128
        };

        Mapper0 {
            prg_rom_data,
            chr_rom_data,
            subtype,
            prg_ram: [0u8; 0x2000], // 8 KiB RAM, but it's 2 or 4 KiB in original cartridge
        }
    }
}

impl Mapper for Mapper0 {
    fn read_cpu_mem(&self, address: u16) -> u8 {
        let address = address as usize;
        match address {
            0x6000..=0x7FFF => self.prg_ram[address - 0x6000],
            0x8000..=0xBFFF => self.prg_rom_data[address - 0x8000],
            0xC000..=0xFFFF => match self.subtype {
                Mapper0Subtype::NRom128 => self.prg_rom_data[address - 0xC000],
                Mapper0Subtype::NRom256 => self.prg_rom_data[address - 0x8000],
            },
            _ => unreachable!("Mapper0 can't map CPU memory address {}", address),
        }
    }

    fn write_cpu_mem(&mut self, address: u16, value: u8) {
        match address {
            0x6000..=0x7FFF => self.prg_ram[address as usize - 0x6000] = value,
            0x8000..=0xFFFF => panic!("Attempt to write to ROM"),
            _ => unreachable!("Mapper0 can't map CPU memory address {}", address),
        }
    }
}
