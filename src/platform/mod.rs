use std::{cell::RefCell, rc::Rc};

use log::{debug, trace};

use crate::rom::INesFormat;

use self::{cpu::CPU, memory::Memory};

pub mod cpu;
pub mod memory;

enum PlatformState {
    NOT_INITIALIZED,
    ROM_LOADED,
    RUNNING,
}

struct Platform {
    state: PlatformState,
    memory: Rc<RefCell<Memory>>,
    cpu: CPU,
}

impl Platform {
    pub fn new() -> Self {
        let memory = Rc::new(RefCell::new([0u8; 65536]));
        let cpu = CPU::new(memory.clone());
        Platform {
            state: PlatformState::NOT_INITIALIZED,
            memory,
            cpu,
        }
    }

    pub fn load_rom_and_run(&mut self, rom_path: &str) {
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
        self.cpu.run()
    }
}

#[cfg(test)]
mod test {
    use log::LevelFilter;

    use super::Platform;

    fn init() {
        let _ = pretty_env_logger::formatted_builder()
            .is_test(true)
            .filter_level(LevelFilter::Trace)
            .try_init();
    }

    #[test]
    fn test_rom_implied() {
        init();

        let mut platform = Platform::new();
        platform.load_rom_and_run("./tests/roms/01-implied.nes");
    }
}
