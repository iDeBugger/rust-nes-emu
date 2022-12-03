use log::debug;

use crate::cartridge::Cartridge;

use self::{
    apu::APU,
    cpu::{CPUContext, CPU},
    ppu::PPU,
};

mod apu;
mod cpu;
mod ppu;

pub struct Platform {
    apu: APU,
    cpu: CPU,
    ppu: PPU,
    cartridge: Option<Cartridge>,
}

impl Platform {
    pub fn new() -> Self {
        let apu = APU::new();
        let cpu = CPU::new();
        let ppu = PPU::new();
        Platform {
            apu,
            cpu,
            ppu,
            cartridge: None,
        }
    }

    pub fn load_rom_and_run(&mut self, rom_path: &str, stop_at_cpu_loop: bool) {
        debug!("Loading ROM at path {}", rom_path);
        let mut cartridge = Cartridge::from_ines(rom_path);
        debug!("ROM loaded");

        let mut ctx = Platform::build_cpu_context(&mut self.ppu, &mut self.apu, &mut cartridge);
        self.cpu.pc = u16::from_le_bytes([
            self.cpu.read_mem(&mut ctx, 0xFFFC),
            self.cpu.read_mem(&mut ctx, 0xFFFD),
        ]);

        self.cartridge = Some(cartridge);

        self.run(stop_at_cpu_loop);
    }

    fn run(&mut self, stop_at_cpu_loop: bool) {
        let cartridge = match &mut self.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };

        loop {
            let mut ctx = Platform::build_cpu_context(&mut self.ppu, &mut self.apu, cartridge);
            if self.cpu.run_step(&mut ctx, stop_at_cpu_loop) {
                break;
            };
            self.apu.run_step();
            // for _ in 0..3 {
            //     self.ppu.run_step();
            // }
        }
    }

    fn build_cpu_context<'ppu, 'apu, 'cartridge>(
        ppu: &'ppu mut PPU,
        apu: &'apu mut APU,
        cartridge: &'cartridge mut Cartridge,
    ) -> CPUContext<'ppu, 'apu, 'cartridge> {
        CPUContext {
            ppu_registers: &mut ppu.registers,
            apu,
            cartidge: cartridge,
        }
    }
}

#[cfg(test)]
mod test {
    use super::Platform;
    use log::{debug, LevelFilter};

    macro_rules! print_rom_result {
        ($platform:tt, $cpu_ctx:tt) => {
            let mut vec_str = vec![];
            let mut n = 0x6004;
            while $platform.cpu.read_mem(&mut $cpu_ctx, n) != 0 {
                vec_str.push($platform.cpu.read_mem(&mut $cpu_ctx, n));
                n += 1;
            }
            let str = vec_str
                .into_iter()
                .map(|byte| byte as char)
                .collect::<String>();
            debug!("\n{}\n", str);
        };
    }

    fn init() {
        let _ = pretty_env_logger::formatted_builder()
            .is_test(true)
            .filter_level(LevelFilter::Debug)
            .try_init();
    }

    #[test]
    fn test_rom_logic_01_basics() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/01-basics.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_02_implied() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/02-implied.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_03_immediate() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/03-immediate.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_04_zero_page() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/04-zero_page.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_05_zp_xy() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/05-zp_xy.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_06_absolute() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/06-absolute.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_07_abs_xy() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/07-abs_xy.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_08_ind_x() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/08-ind_x.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_09_ind_y() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/09-ind_y.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_10_branches() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/10-branches.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_11_stack() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/11-stack.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_12_jmp_jsr() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/12-jmp_jsr.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_13_rts() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/13-rts.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_14_rti() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/14-rti.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_15_brk() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/15-brk.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_logic_16_special() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_logic/16-special.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_rom_timings_1() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/instructions_timings/1-instr_timing.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_apu_1() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/apu/1-len_ctr.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }

    #[test]
    fn test_apu_2() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/apu/2-len_table.nes", true);

        let cartridge = match &mut platform.cartridge {
            Some(cartridge) => cartridge,
            None => panic!("Can't run the platform without a cartridge inserted"),
        };
        let mut ctx = Platform::build_cpu_context(&mut platform.ppu, &mut platform.apu, cartridge);
        print_rom_result!(platform, ctx);

        assert_eq!(platform.cpu.read_mem(&mut ctx, 0x6000), 0x0);
    }
}
