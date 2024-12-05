# `spi-memory-async`

[![crates.io](https://img.shields.io/crates/v/spi-memory-async.svg)](https://crates.io/crates/spi-memory-async)
[![docs.rs](https://docs.rs/spi-memory-async/badge.svg)](https://docs.rs/spi-memory-async/)
[![ci](https://github.com/korken89/spi-memory-async/.github/workflows/rust.yml/badge.svg)](https://github.com/korken89/spi-memory-async/.github/workflows/rust.yml)

This crate provides a generic [`embedded-hal-async`]-based driver for different
families of SPI Flash and EEPROM chips.

Right now, only 25-series Flash chips are supported. Feel free to send PRs to
support other families though!

Please refer to the [changelog](CHANGELOG.md) to see what changed in the last
releases.

[`embedded-hal-async`]: https://github.com/rust-embedded/embedded-hal

## Usage

Add an entry to your `Cargo.toml`:

```toml
[dependencies]
spi-memory-async = "0.1.0"
```

Check the [API Documentation](https://docs.rs/spi-memory-async/) for how to use the
crate's functionality.
