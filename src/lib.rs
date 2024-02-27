//! An [`embedded-hal`]-based SPI-Flash chip driver.
//!
//! This crate aims to be compatible with common families of SPI flash chips.
//! Currently, reading, writing, erasing 25-series chips is supported, and
//! support for other chip families (eg. 24-series chips) is planned.
//!
//! Contributions are welcome!
//!
//! [`embedded-hal`]: https://docs.rs/embedded-hal/

#![doc(html_root_url = "https://docs.rs/spi-memory/0.2.0")]
#![warn(missing_debug_implementations, rust_2018_idioms)]
#![cfg_attr(not(test), no_std)]

mod error;
pub mod prelude;
pub mod series25;
mod utils;

pub use crate::error::Error;

use embedded_hal_async::spi::SpiDevice;

/// A trait for reading operations from a memory chip.
pub trait Read<Addr, SPI: SpiDevice<u8>> {
    /// Reads bytes from a memory chip.
    ///
    /// # Parameters
    /// * `addr`: The address to start reading at.
    /// * `buf`: The buffer to read `buf.len()` bytes into.
    fn read(&mut self, addr: Addr, buf: &mut [u8]) -> Result<(), Error<SPI>>;
}

/// A trait for writing and erasing operations on a memory chip.
pub trait BlockDevice<Addr, SPI: SpiDevice<u8>> {
    /// Erases sectors from the memory chip.
    ///
    /// # Parameters
    /// * `addr`: The address to start erasing at. If the address is not on a sector boundary,
    ///   the lower bits can be ignored in order to make it fit.
    fn erase_sectors(&mut self, addr: Addr, amount: usize) -> Result<(), Error<SPI>>;

    /// Erases the memory chip fully.
    ///
    /// Warning: Full erase operations can take a significant amount of time.
    /// Check your device's datasheet for precise numbers.
    fn erase_all(&mut self) -> Result<(), Error<SPI>>;

    /// Writes bytes onto the memory chip. This method is supposed to assume that the sectors
    /// it is writing to have already been erased and should not do any erasing themselves.
    ///
    /// # Parameters
    /// * `addr`: The address to write to.
    /// * `data`: The bytes to write to `addr`.
    fn write_bytes(&mut self, addr: Addr, data: &mut [u8]) -> Result<(), Error<SPI>>;
}
