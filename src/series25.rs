//! Driver for 25-series SPI Flash and EEPROM chips.

use crate::{utils::HexSlice, Error};
use bitflags::bitflags;
use core::marker::PhantomData;
pub use core::task::Poll;
use core::{convert::TryInto, fmt};
pub use embedded_hal_async::{
    delay::DelayUs,
    spi::{Operation, SpiDevice},
};
pub use embedded_storage_async;

/// 3-Byte JEDEC manufacturer and device identification.
pub struct Identification {
    /// Data collected
    /// - First byte is the manufacturer's ID code from eg JEDEC Publication No. 106AJ
    /// - The trailing bytes are a manufacturer-specific device ID.
    bytes: [u8; 3],

    /// The number of continuations that precede the main manufacturer ID
    continuations: u8,
}

impl Identification {
    /// Build an Identification from JEDEC ID bytes.
    pub fn from_jedec_id(buf: &[u8]) -> Identification {
        // Example response for Cypress part FM25V02A:
        // 7F 7F 7F 7F 7F 7F C2 22 08  (9 bytes)
        // 0x7F is a "continuation code", not part of the core manufacturer ID
        // 0xC2 is the company identifier for Cypress (Ramtron)

        // Find the end of the continuation bytes (0x7F)
        let mut start_idx = 0;
        for (i, item) in buf.iter().enumerate().take(buf.len() - 2) {
            if *item != 0x7F {
                start_idx = i;
                break;
            }
        }

        Self {
            bytes: [buf[start_idx], buf[start_idx + 1], buf[start_idx + 2]],
            continuations: start_idx as u8,
        }
    }

    /// The JEDEC manufacturer code for this chip.
    pub fn mfr_code(&self) -> u8 {
        self.bytes[0]
    }

    /// The manufacturer-specific device ID for this chip.
    pub fn device_id(&self) -> &[u8] {
        self.bytes[1..].as_ref()
    }

    /// Number of continuation codes in this chip ID.
    ///
    /// For example the ARM Ltd identifier is `7F 7F 7F 7F 3B` (5 bytes), so
    /// the continuation count is 4.
    pub fn continuation_count(&self) -> u8 {
        self.continuations
    }
}

impl fmt::Debug for Identification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Identification")
            .field(&HexSlice(self.bytes))
            .finish()
    }
}

#[allow(unused)] // TODO support more features
enum Opcode {
    /// Read the 8-bit legacy device ID.
    ReadDeviceId = 0xAB,
    /// Read the 8-bit manufacturer and device IDs.
    ReadMfDId = 0x90,
    /// Read 16-bit manufacturer ID and 8-bit device ID.
    ReadJedecId = 0x9F,
    /// Set the write enable latch.
    WriteEnable = 0x06,
    /// Clear the write enable latch.
    WriteDisable = 0x04,
    /// Read the 8-bit status register.
    ReadStatus = 0x05,
    /// Write the 8-bit status register. Not all bits are writeable.
    WriteStatus = 0x01,
    Read = 0x03,
    PageProg = 0x02, // directly writes to EEPROMs too
    SectorErase = 0x20,
    BlockErase = 0xD8,
    ChipErase = 0xC7,
}

bitflags! {
    /// Status register bits.
    pub struct Status: u8 {
        /// Erase or write in progress.
        const BUSY = 1 << 0;
        /// Status of the **W**rite **E**nable **L**atch.
        const WEL = 1 << 1;
        /// The 3 protection region bits.
        const PROT = 0b00011100;
        /// **S**tatus **R**egister **W**rite **D**isable bit.
        const SRWD = 1 << 7;
    }
}

/// Trait for defining the size of a flash.
pub trait FlashParameters {
    /// The page write size in bytes.
    const PAGE_SIZE: usize;
    /// The sector erase size in bytes.
    const SECTOR_SIZE: usize;
    /// The block erase size in bytes.
    const BLOCK_SIZE: usize;
    /// The total chip size in bytes.
    const CHIP_SIZE: usize;
}

/// Driver for 25-series SPI Flash chips.
///
/// # Type Parameters
///
/// * **`SPI`**: The SPI master to which the flash chip is attached.
/// * **`FlashParams`**: Memory size.
/// * **`Delay`**: Delay provider.
#[derive(Debug)]
pub struct Flash<SPI, FlashParams, Delay> {
    spi: SPI,
    delay: Delay,
    poll_delay_ms: u32,
    params: PhantomData<FlashParams>,
}

impl<SPI, FlashParams, Delay> Flash<SPI, FlashParams, Delay>
where
    SPI: SpiDevice<u8>,
    Delay: DelayUs,
    FlashParams: FlashParameters,
{
    /// Creates a new 26-series flash driver.
    ///
    /// # Parameters
    ///
    /// * **`spi`**: An SPI master. Must be configured to operate in the correct
    ///   mode for the device.
    /// * **`delay`**: A [`DelayUs`] implementation.
    /// * **`poll_delay_ms`**: The delay between polling the chip when waiting for an operation to complete.
    pub async fn init(
        spi: SPI,
        delay: Delay,
        poll_delay_ms: u32,
        _params: FlashParams,
    ) -> Result<Self, Error<SPI>> {
        let mut this = Flash {
            spi,
            delay,
            poll_delay_ms,
            params: PhantomData,
        };

        // If the MCU is reset and an old operation is still ongoing, wait for it to finish.
        this.wait_done().await?;

        Ok(this)
    }

    /// Get the size of a page which can be written.
    pub fn page_write_size(&self) -> usize {
        FlashParams::PAGE_SIZE
    }

    /// Get the size of a sector which can be erased.
    pub fn sector_erase_size(&self) -> usize {
        FlashParams::SECTOR_SIZE
    }

    /// Get the size of a block which can be erased.
    pub fn block_erase_size(&self) -> usize {
        FlashParams::BLOCK_SIZE
    }

    /// Get the size of the flash chip.
    pub fn chip_size(&self) -> usize {
        FlashParams::CHIP_SIZE
    }

    async fn command_transfer(&mut self, bytes: &mut [u8]) -> Result<(), Error<SPI>> {
        self.spi.transfer_in_place(bytes).await.map_err(Error::Spi)
    }

    async fn command_write(&mut self, bytes: &[u8]) -> Result<(), Error<SPI>> {
        self.spi.write(bytes).await.map_err(Error::Spi)
    }

    /// Reads the JEDEC manufacturer/device identification.
    pub async fn read_jedec_id(&mut self) -> Result<Identification, Error<SPI>> {
        // Optimistically read 12 bytes, even though some identifiers will be shorter
        let mut buf: [u8; 12] = [0; 12];
        buf[0] = Opcode::ReadJedecId as u8;
        self.command_transfer(&mut buf).await?;

        // Skip buf[0] (SPI read response byte)
        Ok(Identification::from_jedec_id(&buf[1..]))
    }

    /// Reads the status register.
    pub async fn read_status(&mut self) -> Result<Status, Error<SPI>> {
        let mut buf = [Opcode::ReadStatus as u8, 0];
        self.command_transfer(&mut buf).await?;

        Ok(Status::from_bits_truncate(buf[1]))
    }

    async fn write_enable(&mut self) -> Result<(), Error<SPI>> {
        let cmd_buf = [Opcode::WriteEnable as u8];
        self.command_write(&cmd_buf).await
    }

    pub async fn wait_done(&mut self) -> Result<(), Error<SPI>> {
        while self.read_status().await?.contains(Status::BUSY) {
            self.delay.delay_ms(self.poll_delay_ms).await;
        }
        Ok(())
    }

    /// Reads flash contents into `buf`, starting at `addr`.
    ///
    /// Note that `addr` is not fully decoded: Flash chips will typically only
    /// look at the lowest `N` bits needed to encode their size, which means
    /// that the contents are "mirrored" to addresses that are a multiple of the
    /// flash size. Only 24 bits of `addr` are transferred to the device in any
    /// case, limiting the maximum size of 25-series SPI flash chips to 16 MiB.
    ///
    /// # Parameters
    ///
    /// * `addr`: 24-bit address to start reading at.
    /// * `buf`: Destination buffer to fill.
    pub async fn read(&mut self, addr: u32, buf: &mut [u8]) -> Result<(), Error<SPI>> {
        // TODO what happens if `buf` is empty?

        let cmd_buf = [
            Opcode::Read as u8,
            (addr >> 16) as u8,
            (addr >> 8) as u8,
            addr as u8,
        ];

        self.spi
            .transaction(&mut [Operation::Write(&cmd_buf), Operation::Read(buf)])
            .await
            .map_err(Error::Spi)
    }

    /// Erases a sector from the memory chip.
    ///
    /// # Parameters
    /// * `addr`: The address to start erasing at. If the address is not on a sector boundary,
    ///   the lower bits can be ignored in order to make it fit.
    pub async fn erase_sector(&mut self, addr: u32) -> Result<(), Error<SPI>> {
        self.write_enable().await?;

        let cmd_buf = [
            Opcode::SectorErase as u8,
            (addr >> 16) as u8,
            (addr >> 8) as u8,
            addr as u8,
        ];
        self.command_write(&cmd_buf).await?;
        self.wait_done().await
    }

    /// Erases a block from the memory chip.
    ///
    /// # Parameters
    /// * `addr`: The address to start erasing at. If the address is not on a block boundary,
    ///   the lower bits can be ignored in order to make it fit.
    pub async fn erase_block(&mut self, addr: u32) -> Result<(), Error<SPI>> {
        self.write_enable().await?;

        let cmd_buf = [
            Opcode::BlockErase as u8,
            (addr >> 16) as u8,
            (addr >> 8) as u8,
            addr as u8,
        ];
        self.command_write(&cmd_buf).await?;
        self.wait_done().await
    }

    /// Writes bytes onto the memory chip. This method is supposed to assume that the sectors
    /// it is writing to have already been erased and should not do any erasing themselves.
    ///
    /// # Parameters
    /// * `addr`: The address to write to.
    /// * `data`: The bytes to write to `addr`, note that it will only take the lowest 256 bytes
    /// from the slice.
    pub async fn write_bytes(&mut self, addr: u32, data: &[u8]) -> Result<(), Error<SPI>> {
        self.write_enable().await?;

        let cmd_buf = [
            Opcode::PageProg as u8,
            (addr >> 16) as u8,
            (addr >> 8) as u8,
            addr as u8,
        ];
        self.spi
            .transaction(&mut [
                Operation::Write(&cmd_buf),
                Operation::Write(&data[..256.min(data.len())]),
            ])
            .await
            .map_err(Error::Spi)?;

        self.wait_done().await
    }

    /// Erases the memory chip fully.
    ///
    /// Warning: Full erase operations can take a significant amount of time.
    /// Check your device's datasheet for precise numbers.
    pub async fn erase_all(&mut self) -> Result<(), Error<SPI>> {
        self.write_enable().await?;
        let cmd_buf = [Opcode::ChipErase as u8];
        self.command_write(&cmd_buf).await?;
        self.wait_done().await
    }

    /// Erases a range of sectors. The range is expressed in bytes. These bytes need to be a multiple of SECTOR_SIZE.
    /// If the range starts at SECTOR_SIZE * 3 then the erase starts at the fourth sector.
    /// All sectors are erased in the range [start_sector..end_sector].
    /// The start address may not be a higher value than the end address.
    ///
    /// # Arguments
    /// * `start_address` - Address of the first byte of the start of the range of sectors that need to be erased.
    /// * `end_address` - Address of the first byte of the end of the range of sectors that need to be erased.
    pub async fn erase_range(
        &mut self,
        start_address: u32,
        end_address: u32,
    ) -> Result<(), Error<SPI>> {
        self.write_enable().await?;
        let sector_size: u32 = FlashParams::SECTOR_SIZE.try_into().unwrap();

        if start_address % sector_size != 0 {
            return Err(Error::NotAligned);
        }

        if end_address % sector_size != 0 {
            return Err(Error::NotAligned);
        }

        if start_address > end_address {
            return Err(Error::OutOfBounds);
        }

        let start_sector = start_address / sector_size;
        let end_sector = end_address / sector_size;

        for sector in start_sector..end_sector {
            self.erase_sector(sector).await.unwrap();
        }

        Ok(())
    }
}

impl<SPI, FlashParams, Delay> embedded_storage::nor_flash::ErrorType
    for Flash<SPI, FlashParams, Delay>
where
    SPI: SpiDevice<u8>,
{
    type Error = Error<SPI>;
}

impl<SPI, FlashParams, Delay> embedded_storage_async::nor_flash::ReadNorFlash
    for Flash<SPI, FlashParams, Delay>
where
    SPI: SpiDevice<u8>,
    Delay: DelayUs,
    FlashParams: FlashParameters,
{
    const READ_SIZE: usize = 1;

    async fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        self.read(offset, bytes).await
    }

    fn capacity(&self) -> usize {
        FlashParams::CHIP_SIZE.try_into().unwrap()
    }
}

impl<SPI, FlashParams, Delay> embedded_storage_async::nor_flash::NorFlash
    for Flash<SPI, FlashParams, Delay>
where
    SPI: SpiDevice<u8>,
    Delay: DelayUs,
    FlashParams: FlashParameters,
{
    const WRITE_SIZE: usize = 1;

    const ERASE_SIZE: usize = FlashParams::SECTOR_SIZE;

    async fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        self.erase_range(from, to).await
    }

    async fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        self.write_bytes(offset, bytes).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_decode_jedec_id() {
        let cypress_id_bytes = [0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0x7F, 0xC2, 0x22, 0x08];
        let ident = Identification::from_jedec_id(&cypress_id_bytes);
        assert_eq!(0xC2, ident.mfr_code());
        assert_eq!(6, ident.continuation_count());
        let device_id = ident.device_id();
        assert_eq!(device_id[0], 0x22);
        assert_eq!(device_id[1], 0x08);
    }
}
