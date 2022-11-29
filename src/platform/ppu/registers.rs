pub struct PPURegisters {
    ppuctrl: u8,
    ppumask: u8,
    ppustatus: u8,
    oamaddr: u8,
    oamdata: u8,
    ppuscroll: u8,
    ppuaddr: u8,
    ppudata: u8,
    oamdma: u8,
}

impl PPURegisters {
    pub fn new() -> Self {
        PPURegisters {
            ppuctrl: 0,
            ppumask: 0,
            ppustatus: 0,
            oamaddr: 0,
            oamdata: 0,
            ppuscroll: 0,
            ppuaddr: 0,
            ppudata: 0,
            oamdma: 0,
        }
    }

    pub fn read_ppuctrl(&self) -> u8 {
        self.ppuctrl
    }

    pub fn write_ppuctrl(&mut self, data: u8) {
        self.ppuctrl = data;
    }

    pub fn read_ppumask(&self) -> u8 {
        self.ppumask
    }

    pub fn write_ppumask(&mut self, data: u8) {
        self.ppumask = data;
    }

    pub fn read_ppustatus(&self) -> u8 {
        self.ppuctrl
    }

    pub fn write_ppustatus(&mut self, data: u8) {
        self.ppuctrl = data;
    }

    pub fn read_oamaddr(&self) -> u8 {
        self.oamaddr
    }

    pub fn write_oamaddr(&mut self, data: u8) {
        self.oamaddr = data;
    }

    pub fn read_oamdata(&self) -> u8 {
        self.oamdata
    }

    pub fn write_oamdata(&mut self, data: u8) {
        self.oamdata = data;
    }

    pub fn read_ppuscroll(&self) -> u8 {
        self.ppuscroll
    }

    pub fn write_ppuscroll(&mut self, data: u8) {
        self.ppuscroll = data;
    }

    pub fn read_ppuaddr(&self) -> u8 {
        self.ppuaddr
    }

    pub fn write_ppuaddr(&mut self, data: u8) {
        self.ppuaddr = data;
    }

    pub fn read_ppudata(&self) -> u8 {
        self.ppudata
    }

    pub fn write_ppudata(&mut self, data: u8) {
        self.ppudata = data;
    }

    pub fn read_oamdma(&self) -> u8 {
         self.oamdma
    }

    pub fn write_oamdma(&mut self, data: u8) {
        self.oamdma = data;
    }
}
