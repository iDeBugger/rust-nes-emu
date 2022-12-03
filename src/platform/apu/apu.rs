const LENGTH_TABLE: [u8; 0x20] = [
    10, 254, 20, 2, 40, 4, 80, 6, 160, 8, 60, 10, 14, 12, 26, 14, 12, 16, 24, 18, 48, 20, 96, 22,
    192, 24, 72, 26, 16, 28, 32, 30,
];

const STEP4_SEQUENCER_RESET: u32 = 29830;
const STEP4_SEQUENCER_HALF_FRAMES: [u32; 2] = [14913, 29829];
const STEP4_SEQUENCER_IRQ_FRAMES: [u32; 3] = [29828, 29829, 29830];

const STEP5_SEQUENCER_RESET: u32 = 37282;
const STEP5_SEQUENCER_HALF_FRAMES: [u32; 2] = [14913, 37281];

enum SequencerMode {
    Step4,
    Step5,
}

pub struct APU {
    sequencer: u32,
    sequence_mode: SequencerMode,

    pulse1_length_counter: u8,
    pulse1_length_counter_halted: bool,
    pulse1_length_counter_enabled: bool,
    pulse2_length_counter: u8,
    pulse2_length_counter_halted: bool,
    pulse2_length_counter_enabled: bool,
    triangle_length_counter: u8,
    triangle_length_counter_halted: bool,
    triangle_length_counter_enabled: bool,
    noise_length_counter: u8,
    noise_length_counter_halted: bool,
    noise_length_counter_enabled: bool,
}

impl APU {
    pub fn new() -> Self {
        APU {
            sequencer: 0,
            sequence_mode: SequencerMode::Step4,
            pulse1_length_counter: 0,
            pulse1_length_counter_halted: false,
            pulse1_length_counter_enabled: false,
            pulse2_length_counter: 0,
            pulse2_length_counter_halted: false,
            pulse2_length_counter_enabled: false,
            triangle_length_counter: 0,
            triangle_length_counter_halted: false,
            triangle_length_counter_enabled: false,
            noise_length_counter: 0,
            noise_length_counter_halted: false,
            noise_length_counter_enabled: false,
        }
    }

    pub fn write_pulse1_1(&mut self, value: u8) {
        self.pulse1_length_counter_halted = value & 0b0010_0000 > 0;
    }

    pub fn write_pulse1_4(&mut self, value: u8) {
        let _timer_high = value & 0b0000_0111;

        if self.pulse1_length_counter_enabled {
            let length_counter_load = (value & 0b1111_1000) >> 3;
            self.pulse1_length_counter = LENGTH_TABLE[length_counter_load as usize];
        } else {
            self.pulse1_length_counter = 0;
        }
    }

    pub fn write_pulse2_1(&mut self, value: u8) {
        self.pulse2_length_counter_halted = value & 0b0010_0000 > 0;
    }

    pub fn write_pulse2_4(&mut self, value: u8) {
        let _timer_high = value & 0b0000_0111;

        if self.pulse2_length_counter_enabled {
            let length_counter_load = (value & 0b1111_1000) >> 3;
            self.pulse2_length_counter = LENGTH_TABLE[length_counter_load as usize];
        } else {
            self.pulse1_length_counter = 0;
        }
    }

    pub fn write_noise_1(&mut self, value: u8) {
        self.noise_length_counter_halted = value & 0b0010_0000 > 0;
    }

    pub fn write_noise_4(&mut self, value: u8) {
        let _timer_high = value & 0b0000_0111;

        if self.noise_length_counter_enabled {
            let length_counter_load = (value & 0b1111_1000) >> 3;
            self.noise_length_counter = LENGTH_TABLE[length_counter_load as usize];
        } else {
            self.pulse1_length_counter = 0;
        }
    }

    pub fn write_triangle_1(&mut self, value: u8) {
        self.triangle_length_counter_halted = value & 0b1000_0000 > 0;
    }

    pub fn write_triangle_4(&mut self, value: u8) {
        let _timer_high = value & 0b0000_0111;

        if self.triangle_length_counter_enabled {
            let length_counter_load = (value & 0b1111_1000) >> 3;
            self.triangle_length_counter = LENGTH_TABLE[length_counter_load as usize];
        } else {
            self.pulse1_length_counter = 0;
        }
    }

    pub fn read_status_register(&self) -> u8 {
        let mut status = 0;
        status |= match self.noise_length_counter {
            0 => 0,
            _ => 0b0000_1000,
        };
        status |= match self.triangle_length_counter {
            0 => 0,
            _ => 0b0000_0100,
        };
        status |= match self.pulse2_length_counter {
            0 => 0,
            _ => 0b0000_0010,
        };
        status |= match self.pulse1_length_counter {
            0 => 0,
            _ => 0b0000_0001,
        };
        status
    }

    pub fn write_status_register(&mut self, value: u8) {
        self.noise_length_counter_enabled = value & 0b0000_1000 > 0;
        if !self.noise_length_counter_enabled {
            self.noise_length_counter = 0;
        }

        self.triangle_length_counter_enabled = value & 0b0000_0100 > 0;
        if !self.triangle_length_counter_enabled {
            self.triangle_length_counter = 0;
        }

        self.pulse2_length_counter_enabled = value & 0b0000_0010 > 0;
        if !self.pulse2_length_counter_enabled {
            self.pulse2_length_counter = 0;
        }

        self.pulse1_length_counter_enabled = value & 0b0000_0001 > 0;
        if !self.pulse1_length_counter_enabled {
            self.pulse1_length_counter = 0;
        }
    }

    pub fn write_frame_counter_register(&mut self, value: u8) {
        if value & 0b1000_0000 > 0 {
            self.sequence_mode = SequencerMode::Step5;
            self.process_length_counters();
        } else {
            self.sequence_mode = SequencerMode::Step4;
        }
        self.sequencer = 0;
    }

    pub fn run_step(&mut self) {
        match self.sequence_mode {
            SequencerMode::Step4 => self.run_step_mode_step4(),
            SequencerMode::Step5 => self.run_step_mode_step5(),
        }
        self.sequencer += 1;
    }

    fn run_step_mode_step4(&mut self) {
        match self.sequencer {
            x if STEP4_SEQUENCER_HALF_FRAMES.contains(&x) => self.process_length_counters(),
            STEP4_SEQUENCER_RESET => self.sequencer = 0,
            _ => {}
        }
    }

    fn run_step_mode_step5(&mut self) {
        match self.sequencer {
            x if STEP5_SEQUENCER_HALF_FRAMES.contains(&x) => self.process_length_counters(),
            STEP5_SEQUENCER_RESET => self.sequencer = 0,
            _ => {}
        }
    }

    fn process_length_counters(&mut self) {
        if self.pulse1_length_counter_enabled
            && self.pulse1_length_counter > 0
            && !self.pulse1_length_counter_halted
        {
            self.pulse1_length_counter -= 1;
        }

        if self.pulse2_length_counter_enabled
            && self.pulse2_length_counter > 0
            && !self.pulse2_length_counter_halted
        {
            self.pulse2_length_counter -= 1;
        }

        if self.noise_length_counter_enabled
            && self.noise_length_counter > 0
            && !self.noise_length_counter_halted
        {
            self.noise_length_counter -= 1;
        }

        if self.triangle_length_counter_enabled
            && self.triangle_length_counter > 0
            && !self.triangle_length_counter_halted
        {
            self.triangle_length_counter -= 1;
        }
    }
}
