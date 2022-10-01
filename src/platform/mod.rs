use std::{cell::RefCell, rc::Rc};

use log::{debug, trace};

use crate::rom::INesFormat;

use self::{cpu::CPU, memory::Memory, ppu::PPU};

pub mod cpu;
pub mod memory;
pub mod ppu;

enum PlatformState {
    NOT_INITIALIZED,
    ROM_LOADED,
    RUNNING,
}

struct Platform {
    state: PlatformState,
    memory: Rc<RefCell<Memory>>,
    cpu: CPU,
    ppu: PPU,
}

impl Platform {
    pub fn new() -> Self {
        let memory = Rc::new(RefCell::new([0u8; 65536]));
        let cpu = CPU::new(memory.clone());
        let ppu = PPU::new(memory.clone());
        Platform {
            state: PlatformState::NOT_INITIALIZED,
            memory,
            cpu,
            ppu,
        }
    }

    pub fn load_rom_and_run(&mut self, rom_path: &str, stop_at_cpu_loop: bool) {
        debug!("Loading ROM at path {}", rom_path);
        let rom = INesFormat::from_file(rom_path);
        debug!("ROM loaded");

        let start = {
            debug!("Borrowing the memory...");
            let mut memory = self.memory.borrow_mut();
            debug!("Loading ROM PRG data into the memory...");
            for (i, byte) in rom.rom.prg_rom_data.iter().take(16 * 1024).enumerate() {
                memory[0x8000 + i] = *byte;
            }
            for (i, byte) in rom.rom.prg_rom_data.iter().skip(16 * 1024).enumerate() {
                memory[0xC000 + i] = *byte;
            }
            trace!("ROM PRG data: {:#X?}", rom.rom.prg_rom_data);
            debug!("ROM PRG data is loaded into the memory");

            u16::from_le_bytes([memory[0xFFFC], memory[0xFFFD]])
        };
        debug!("CPU program counter value from 0xFFFC: {:#06X}", start);

        self.cpu.pc = start;

        self.run(stop_at_cpu_loop);
    }

    fn run(&mut self, stop_at_cpu_loop: bool) {
        loop {
            if self.cpu.run_step(stop_at_cpu_loop) {
                break;
            };
            // for _ in 0..3 {
            //     self.ppu.run_step();
            // }
        }
    }
}

#[cfg(test)]
mod test {
    use super::Platform;
    use log::{debug, LevelFilter};

    macro_rules! print_rom_result {
        ($mem:tt) => {
            let mut vec_str = vec![];
            let mut n = 0x6004;
            while $mem[n] != 0 {
                vec_str.push($mem[n]);
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
    fn test_rom_01_basics() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/01-basics.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_02_implied() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/02-implied.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_03_immediate() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/03-immediate.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_04_zero_page() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/04-zero_page.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_05_zp_xy() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/05-zp_xy.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_06_absolute() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/06-absolute.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_07_abs_xy() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/07-abs_xy.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_08_ind_x() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/08-ind_x.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_09_ind_y() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/09-ind_y.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_10_branches() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/10-branches.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_11_stack() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/11-stack.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_12_jmp_jsr() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/12-jmp_jsr.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_13_rts() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/13-rts.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_14_rti() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/14-rti.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }

    #[test]
    fn test_rom_15_brk() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/15-brk.nes", true);

        let mem = platform.memory.borrow();
        print_rom_result!(mem);
        assert_eq!(mem[0x6000], 0x0);
    }
}
