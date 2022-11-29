pub struct PPUMemory {
    pattern_table_0: [u8; 0x1000],
    pattern_table_1: [u8; 0x1000],
    nametable_0: [u8; 0x0400],
    nametable_1: [u8; 0x0400],
    nametable_2: [u8; 0x0400],
    nametable_3: [u8; 0x0400],
    palettes: [u8; 0x0020],
    oam: [[u8; 4]; 64],
}
