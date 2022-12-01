use nom::{
    bytes::streaming::{tag, take},
    IResult,
};

pub struct iNes {
    pub prg_rom_data: Vec<u8>,
    pub chr_rom_data: Vec<u8>,
}

struct iNesHeader {
    prg_rom_size: u8,
    chr_rom_size: u8,
}

const PRG_BLOCK_SIZE: u16 = 16384;
const CHR_BLOCK_SIZE: u16 = 8192;

impl iNes {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        match Self::parse_rom(bytes) {
            Ok((_, rom)) => rom,
            Err(_) => panic!("Failed to load ROM"),
        }
    }

    fn parse_rom(i: &[u8]) -> IResult<&[u8], iNes> {
        let (i, header) = Self::parse_header(i)?;
        let (i, prg_rom_data) = take(PRG_BLOCK_SIZE * header.prg_rom_size as u16)(i)?;
        let (i, chr_rom_data) = take(CHR_BLOCK_SIZE * header.chr_rom_size as u16)(i)?;

        let rom = iNes {
            prg_rom_data: Vec::from(prg_rom_data),
            chr_rom_data: Vec::from(chr_rom_data),
        };
        Ok((i, rom))
    }

    fn parse_header(i: &[u8]) -> IResult<&[u8], iNesHeader> {
        let (i, _) = tag(&[0x4E, 0x45, 0x53, 0x1A])(i)?;
        let (i, prg_rom_size) = take(1usize)(i)?;
        let (i, chr_rom_size) = take(1usize)(i)?;
        let (i, _) = take(10usize)(i)?;

        let header = iNesHeader {
            prg_rom_size: prg_rom_size[0],
            chr_rom_size: chr_rom_size[0],
        };
        Ok((i, header))
    }
}
