mod mapper0;

pub use mapper0::Mapper0;

pub trait Mapper {
    fn read_cpu_mem(&self, address: u16) -> u8;
    fn write_cpu_mem(&mut self, address: u16, value: u8);
}
