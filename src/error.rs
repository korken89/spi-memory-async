use core::fmt::{self, Debug, Display};
use embedded_hal_async::spi::SpiDevice;
use embedded_storage::nor_flash::NorFlashError;

/// The error type used by this library.
///
/// This can encapsulate an SPI error, and adds its own protocol errors
/// on top of that.
#[non_exhaustive]
pub enum Error<SPI: SpiDevice<u8>> {
    /// The arguments are not properly aligned.
    NotAligned,
    /// The arguments are out of bounds.
    OutOfBounds,
    /// An SPI transfer failed.
    Spi(SPI::Error),
    /// Status register contained unexpected flags.
    ///
    /// This can happen when the chip is faulty, incorrectly connected, or the
    /// driver wasn't constructed or destructed properly (eg. while there is
    /// still a write in progress).
    UnexpectedStatus,
}

impl<SPI: SpiDevice<u8>> NorFlashError for Error<SPI> {
    fn kind(&self) -> embedded_storage::nor_flash::NorFlashErrorKind {
        use embedded_storage::nor_flash::NorFlashErrorKind;
        match self {
            Error::NotAligned => NorFlashErrorKind::NotAligned,
            Error::OutOfBounds => NorFlashErrorKind::OutOfBounds,
            Error::Spi(_) => NorFlashErrorKind::Other,
            Error::UnexpectedStatus => NorFlashErrorKind::Other,
        }
    }
}

impl<SPI: SpiDevice<u8>> Debug for Error<SPI> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::NotAligned => f.write_str("Error::NotAligned"),
            Error::OutOfBounds => f.write_str("Error::OutOfBounds"),
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
            Error::NotAligned => f.write_str("arguments are not properly aligned"),
            Error::OutOfBounds => f.write_str("arguments are out of bounds"),
            Error::Spi(spi) => write!(f, "SPI error: {}", spi),
            Error::UnexpectedStatus => f.write_str("unexpected value in status register"),
        }
    }
}

impl<SPI: SpiDevice<u8>> defmt::Format for Error<SPI>
where
    SPI::Error: defmt::Format,
{
    fn format(&self, f: defmt::Formatter<'_>) {
        match self {
            Error::NotAligned => defmt::write!(f, "arguments are not properly aligned"),
            Error::OutOfBounds => defmt::write!(f, "arguments are out of bounds"),
            Error::Spi(spi) => defmt::write!(f, "SPI error: {}", spi),
            Error::UnexpectedStatus => defmt::write!(f, "unexpected value in status register"),
        }
    }
}
