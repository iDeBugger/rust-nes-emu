use self::parsers::ines::iNes;
use std::{
    fs::{self, File},
    io::Read,
};

mod parsers;

pub struct INesFormat {
    pub rom: iNes,
}

impl INesFormat {
    pub fn from_file(path: &str) -> Self {
        let mut f = File::open(path).expect("File not found");
        let metadata = fs::metadata(path).expect("Unable to read file metadata");
        let mut buffer = vec![0; metadata.len() as usize];
        f.read(&mut buffer)
            .expect("File read failed: buffer overflow");

        let rom = iNes::from_bytes(&buffer);

        INesFormat { rom }
    }
}
