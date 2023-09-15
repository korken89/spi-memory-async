use core::fmt::{self, Debug, Display};
use embedded_hal_async::spi::SpiDevice;

mod private {
    #[derive(Debug)]
    pub enum Private {}
}

/// The error type used by this library.
///
/// This can encapsulate an SPI error, and adds its own protocol errors
/// on top of that.
#[non_exhaustive]
pub enum Error<SPI: SpiDevice<u8>> {
    /// An SPI transfer failed.
    Spi(SPI::Error),

    /// Status register contained unexpected flags.
    ///
    /// This can happen when the chip is faulty, incorrectly connected, or the
    /// driver wasn't constructed or destructed properly (eg. while there is
    /// still a write in progress).
    UnexpectedStatus,
}

impl<SPI: SpiDevice<u8>> Debug for Error<SPI> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Spi(spi) => write!(f, "Error::Spi({:?})", spi),
            Error::UnexpectedStatus => f.write_str("Error::UnexpectedStatus"),
        }
    }
}

impl<SPI: SpiDevice<u8>> Display for Error<SPI>
where
    SPI::Error: Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Spi(spi) => write!(f, "SPI error: {}", spi),
            Error::UnexpectedStatus => f.write_str("unexpected value in status register"),
        }
    }
}
