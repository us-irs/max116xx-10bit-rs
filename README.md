[![Crates.io](https://img.shields.io/crates/v/max116xx-10bit)](https://crates.io/crates/max116xx-10bit)
[![build](https://github.com/us-irs/max116xx-10bit-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/us-irs/max116xx-10bit-rs/actions/workflows/ci.yml)
[![docs.rs](https://img.shields.io/docsrs/max116xx-10bit)](https://docs.rs/max116xx-10bit)

Rust Maxim 116xx 10-bit ADC device driver crate
========

This is a platform agnostic Rust driver for the MAX11618-MAX11621, MAX11624 and MAX11625 10-bit
[ADC devices](https://www.maximintegrated.com/en/products/analog/data-converters/analog-to-digital-converters/MAX11619.html)
which uses the [`embedded-hal`](https://github.com/rust-embedded/embedded-hal) traits.

This driver implements basic operations to read raw ADC values:

- Read ADC values using the SPI clock as an external clock
- Read ADC values using the End-Of-Conversion (EOC) pin

Currently, the driver only supports operation without a wake-up delay and the EOC read
functionality is still limited. Pull requests to improve this are welcome.

# Usage

To use this driver, import this crate and an `embedded-hal` implementation and then instantiate
the appropriate device.

The crate uses basic type-level support to prevent using the ADC in a wrong way.
The type-level support defaults to an externally clocked device with no wake-up delay.

This crate was tested using the Vorago REB1 development board. You can find an example application
[here](https://egit.irs.uni-stuttgart.de/rust/vorago-reb1/src/branch/main/src/max11619.rs)
and [here](https://egit.irs.uni-stuttgart.de/rust/vorago-reb1/src/branch/main/examples/max11619-adc.rs).
