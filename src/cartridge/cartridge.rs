use std::{
    fs::{self, File},
    io::Read,
};

use super::{
    mappers::{Mapper, Mapper0},
    parsers::ines::iNes,
};

pub struct Cartridge {
    mapper: Box<dyn Mapper>,
}

impl Cartridge {
    pub fn from_ines(path: &str) -> Self {
        let mut f = File::open(path).expect("File not found");
        let metadata = fs::metadata(path).expect("Unable to read file metadata");
        let mut buffer = vec![0; metadata.len() as usize];
        f.read(&mut buffer)
            .expect("File read failed: buffer overflow");

        let ines = iNes::from_bytes(&buffer);
        let mapper = Mapper0::new(ines.prg_rom_data, ines.chr_rom_data);

        Cartridge {
            mapper: Box::new(mapper),
        }
    }

    pub fn read_cpu_mem(&self, address: u16) -> u8 {
        self.mapper.read_cpu_mem(address)
    }

    pub fn write_cpu_mem(&mut self, address: u16, value: u8) {
        self.mapper.write_cpu_mem(address, value)
    }
}
