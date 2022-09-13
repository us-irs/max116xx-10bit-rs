//! Type-Safe API to use the MAX116xx 10-bit ADC devices
//!
//! ## Usage
//!
//! You can create an initial ADC struct by using the [`Max116xx10Bit::max11618`],
//! [`Max116xx10Bit::max11619`], [`Max116xx10Bit::max11620`], [`Max116xx10Bit::max11621`],
//! [`Max116xx10Bit::max11624`] and [`Max116xx10Bit::max11625`] functions depending on which device
//! you are using. This automatically sets the highest channel number accordingly.
//!
//! The default structs use the externally clocked mode with an external voltage reference.
//! You can modify the operation mode of the ADC by converting the default struct using the
//! following functions
//!
//!  - [`Max116xx10Bit::into_ext_clkd_with_int_ref_no_wakeup_delay`]
//!  - [`Max116xx10Bit::into_ext_clkd_with_int_ref_wakeup_delay`]
//!  - [`Max116xx10Bit::into_int_clkd_int_timed_through_ser_if_with_wakeup`]
//!  - [`Max116xx10Bit::into_int_clkd_int_timed_through_ser_if_without_wakeup`]
//!
//! ## Examples
//!
//! You can find an example application [here](https://egit.irs.uni-stuttgart.de/rust/vorago-reb1/src/branch/main/examples/max11619-adc.rs)
//! using a [thin abstraction layer](https://egit.irs.uni-stuttgart.de/rust/vorago-reb1/src/branch/main/src/max11619.rs)
#![no_std]
use core::{marker::PhantomData, slice::IterMut};
use embedded_hal::{
    blocking::delay::DelayUs,
    blocking::spi::Transfer,
    digital::v2::{InputPin, OutputPin},
    spi::FullDuplex,
};

//==================================================================================================
// Type-level support
//==================================================================================================

pub trait HasChannels: private::Sealed {
    const NUM: u8;
}

struct Max11618;
struct Max11619;
struct Max11620;
struct Max11621;
struct Max11624;
struct Max11625;

pub struct WithWakeupDelay;
pub struct WithoutWakeupDelay;

pub trait WakeupDelay: private::Sealed {
    const ON: bool;
}

impl WakeupDelay for WithWakeupDelay {
    const ON: bool = true;
}
impl private::Sealed for WithWakeupDelay {}
impl WakeupDelay for WithoutWakeupDelay {
    const ON: bool = false;
}
impl private::Sealed for WithoutWakeupDelay {}

impl private::Sealed for Max11618 {}
impl HasChannels for Max11618 {
    const NUM: u8 = 4;
}

impl private::Sealed for Max11619 {}
impl HasChannels for Max11619 {
    const NUM: u8 = 4;
}

impl private::Sealed for Max11620 {}
impl HasChannels for Max11620 {
    const NUM: u8 = 8;
}

impl private::Sealed for Max11621 {}
impl HasChannels for Max11621 {
    const NUM: u8 = 8;
}

impl private::Sealed for Max11624 {}
impl HasChannels for Max11624 {
    const NUM: u8 = 16;
}

impl private::Sealed for Max11625 {}
impl HasChannels for Max11625 {
    const NUM: u8 = 16;
}

pub trait Clocked: private::Sealed {
    const CLK_SEL: ClockMode;
}

pub trait InternallyClocked: Clocked {}

pub struct InternallyClockedInternallyTimedCnvst {}
impl private::Sealed for InternallyClockedInternallyTimedCnvst {}
impl Clocked for InternallyClockedInternallyTimedCnvst {
    const CLK_SEL: ClockMode = ClockMode::InternalClockInternallyTimedCnvst;
}
impl InternallyClocked for InternallyClockedInternallyTimedCnvst {}
type IntClkdIntTmdCnvst = InternallyClockedInternallyTimedCnvst;

pub struct InternallyClockedExternallyTimedCnvst {}
impl private::Sealed for InternallyClockedExternallyTimedCnvst {}
impl Clocked for InternallyClockedExternallyTimedCnvst {
    const CLK_SEL: ClockMode = ClockMode::InternalClockExternallyTimedCnvst;
}
impl InternallyClocked for InternallyClockedExternallyTimedCnvst {}
type IntClkdExtTmdCnvst = InternallyClockedExternallyTimedCnvst;

pub struct InternallyClockedInternallyTimedSerialInterface {}
impl private::Sealed for InternallyClockedInternallyTimedSerialInterface {}
impl Clocked for InternallyClockedInternallyTimedSerialInterface {
    const CLK_SEL: ClockMode = ClockMode::InternalClockInternallyTimedSerialInterface;
}
impl InternallyClocked for InternallyClockedInternallyTimedSerialInterface {}
type IntClkdIntTmdSerIF = InternallyClockedInternallyTimedSerialInterface;

pub struct ExternallyClocked {}
impl private::Sealed for ExternallyClocked {}
impl Clocked for ExternallyClocked {
    const CLK_SEL: ClockMode = ClockMode::ExternalClockExternallyTimedSclk;
}
type ExtClkd = ExternallyClocked;

//==================================================================================================
// Definitions
//==================================================================================================

/// Clock modes for the MAX116XX devices
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ClockMode {
    /// Internally timed, CNVST only needs to be pulsed for 40ns.
    /// CNVST Configuration: CNVST active low
    InternalClockInternallyTimedCnvst = 0b00,
    /// Externally timed through CNVST. CNVST needs to be held low for the conversion duration,
    /// whigh might include the wake-up delay. CNVST Configuration: CNVST active low
    InternalClockExternallyTimedCnvst = 0b01,
    /// Start conversions using the serial interface instead of CNVST.
    /// Default mode at power-up. CNVST Configuration: AIN15/AIN11/AIN7
    InternalClockInternallyTimedSerialInterface = 0b10,
    /// Use the SPI clock as the conversion clock
    ExternalClockExternallyTimedSclk = 0b11,
}

/// Voltage reference modes
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VoltageRefMode {
    /// Auto-Shutdown is on, wake-up delay of 65 us
    InternalRefWithWakeupDelay = 0b00,
    ExternalSingleEndedNoWakeupDelay = 0b01,
    InternalRefWithoutWakeupDelay = 0b10,
}

/// Specifies how many conversions are performed and then averaged for each
/// requested result
pub enum AveragingConversions {
    OneConversion = 0b000,
    FourConversions = 0b100,
    EightConversions = 0b101,
    SixteenConversions = 0b110,
    ThirtytwoConversions = 0b111,
}

/// Specifies the number of returned result in single scan mode
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum AveragingResults {
    FourResults = 0b00,
    EightResults = 0b01,
    TwelveResults = 0b10,
    SixteenResults = 0b11,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum ScanMode {
    Scan0ToChannelN = 0b00,
    ScanChannelNToHighest = 0b01,
    ScanChannelNRepeatedly = 0b10,
    ConvertChannelNOnce = 0b11,
}

#[derive(Debug)]
pub enum AdcError {
    InvalidChannel,
    InvalidRefMode,
    CmdBufTooSmall,
    ResulBufTooSmall,
    /// Other pending operation (possible of other type)
    PendingOperation,
    NoPendingOperation,
    InvalidClockMode,
}

#[derive(Debug)]
pub enum Error<SpiE, PinE> {
    Adc(AdcError),
    Spi(SpiE),
    Pin(PinE),
}

impl<SpiE, PinE> From<AdcError> for Error<SpiE, PinE> {
    fn from(other: AdcError) -> Self {
        Error::Adc(other)
    }
}

struct InternalCfg {
    clk_mode: ClockMode,
    ref_mode: VoltageRefMode,
    pending_scan_mode: Option<ScanMode>,
    max_channels: u8,
    results_len: u8,
    requested_conversions: usize,
}
//==================================================================================================
// ADC implementation
//==================================================================================================

pub struct Max116xx10Bit<SPI, CS, CLOCKED = ExtClkd, WAKEUP = WithoutWakeupDelay> {
    spi: SPI,
    cs: CS,
    cfg: InternalCfg,
    clocked: PhantomData<CLOCKED>,
    delay: PhantomData<WAKEUP>,
}

pub struct Max116xx10BitEocExt<SPI, CS, EOC, CLOCKED> {
    base: Max116xx10Bit<SPI, CS, CLOCKED, WithoutWakeupDelay>,
    eoc: EOC,
}

pub struct Max116xx10BitCnvstEocExt<SPI, CS, EOC, CNVST, CLOCKED, WAKEUP = WithoutWakeupDelay> {
    base: Max116xx10Bit<SPI, CS, CLOCKED, WAKEUP>,
    eoc: EOC,
    cnvst: CNVST,
}

//==================================================================================================
// Generic
//==================================================================================================

impl<SpiE, PinE, CS, SPI> Max116xx10Bit<SPI, CS, ExtClkd, WithoutWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    pub fn max11618(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11618>(spi, cs)
    }
    pub fn max11619(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11619>(spi, cs)
    }
    pub fn max11620(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11620>(spi, cs)
    }
    pub fn max11621(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11621>(spi, cs)
    }
    pub fn max11624(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11624>(spi, cs)
    }
    pub fn max11625(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        Self::new::<Max11625>(spi, cs)
    }

    /// Create a new generic MAX116xx instance. By default the generated ADC struct is configured
    /// for externally clocked mode with conversions timed through the serial interface and
    /// an external voltage reference. You can convert the ADC to use other SETUP register
    /// configurations using the `into*` functions.
    ///
    /// The corresponding SETUP register is `0b0111_0100`
    /// Please note that you still might have to reset and setup the ADC.
    pub fn new<MAX: HasChannels>(spi: SPI, cs: CS) -> Result<Self, Error<SpiE, PinE>> {
        let max_dev = Max116xx10Bit {
            spi,
            cs,
            cfg: InternalCfg {
                clk_mode: ExtClkd::CLK_SEL,
                ref_mode: VoltageRefMode::ExternalSingleEndedNoWakeupDelay,
                pending_scan_mode: None,
                max_channels: MAX::NUM,
                results_len: Self::get_results_len(AveragingResults::FourResults),
                requested_conversions: 0,
            },
            delay: PhantomData,
            clocked: PhantomData,
        };
        Ok(max_dev)
    }

    /// Use internal reference which is off after scan. This means that the device needs a wakeup
    /// delay
    ///
    /// The corresponding SETUP register is `0b0111_0000`
    pub fn into_ext_clkd_with_int_ref_wakeup_delay(
        self,
    ) -> Max116xx10Bit<SPI, CS, ExtClkd, WithWakeupDelay> {
        Max116xx10Bit {
            spi: self.spi,
            cs: self.cs,
            cfg: InternalCfg {
                clk_mode: ExtClkd::CLK_SEL,
                ref_mode: VoltageRefMode::InternalRefWithWakeupDelay,
                pending_scan_mode: None,
                max_channels: self.cfg.max_channels,
                results_len: Self::get_results_len(AveragingResults::FourResults),
                requested_conversions: 0,
            },
            clocked: PhantomData,
            delay: PhantomData,
        }
    }

    /// Use SPI clock as conversion clock and use the internal voltage reference without a wakeup
    /// delay
    ///
    /// The corresponding SETUP register is `0b0111_1000`
    pub fn into_ext_clkd_with_int_ref_no_wakeup_delay(
        self,
    ) -> Max116xx10Bit<SPI, CS, ExtClkd, WithoutWakeupDelay> {
        Max116xx10Bit {
            spi: self.spi,
            cs: self.cs,
            cfg: InternalCfg {
                clk_mode: ExtClkd::CLK_SEL,
                ref_mode: VoltageRefMode::InternalRefWithoutWakeupDelay,
                pending_scan_mode: None,
                max_channels: self.cfg.max_channels,
                results_len: Self::get_results_len(AveragingResults::FourResults),
                requested_conversions: 0,
            },
            clocked: PhantomData,
            delay: PhantomData,
        }
    }

    /// Convert into interally clocked mode with internal timing initiated by the serial interface
    /// and a wakeup delay. This can be used to reduce power consumption
    ///
    /// The corresponding SETUP register is `0b0110_1100`
    pub fn into_int_clkd_int_timed_through_ser_if_with_wakeup<EOC: InputPin<Error = PinE>>(
        self,
        eoc: EOC,
    ) -> Max116xx10BitEocExt<SPI, CS, EOC, IntClkdIntTmdSerIF> {
        Max116xx10BitEocExt {
            base: Max116xx10Bit {
                spi: self.spi,
                cs: self.cs,
                cfg: InternalCfg {
                    clk_mode: IntClkdIntTmdSerIF::CLK_SEL,
                    ref_mode: VoltageRefMode::InternalRefWithWakeupDelay,
                    pending_scan_mode: None,
                    max_channels: self.cfg.max_channels,
                    results_len: Self::get_results_len(AveragingResults::FourResults),
                    requested_conversions: 0,
                },
                clocked: PhantomData,
                delay: PhantomData,
            },
            eoc,
        }
    }

    /// Convert into interally clocked mode with internal timing initiated by the serial interface
    /// and no wakeup delay.
    ///
    /// The corresponding SETUP register can be one of the two
    ///  - External Voltage reference: `0b0110_0100`
    ///  - Internal Voltage reference always on: `0b0110_1000`
    pub fn into_int_clkd_int_timed_through_ser_if_without_wakeup<EOC: InputPin<Error = PinE>>(
        self,
        v_ref: VoltageRefMode,
        eoc: EOC,
    ) -> Result<Max116xx10BitEocExt<SPI, CS, EOC, IntClkdIntTmdSerIF>, AdcError> {
        if v_ref == VoltageRefMode::InternalRefWithWakeupDelay {
            return Err(AdcError::InvalidRefMode);
        }
        Ok(Max116xx10BitEocExt {
            base: Max116xx10Bit {
                spi: self.spi,
                cs: self.cs,
                cfg: InternalCfg {
                    clk_mode: IntClkdIntTmdSerIF::CLK_SEL,
                    ref_mode: VoltageRefMode::InternalRefWithWakeupDelay,
                    pending_scan_mode: None,
                    max_channels: self.cfg.max_channels,
                    results_len: Self::get_results_len(AveragingResults::FourResults),
                    requested_conversions: 0,
                },
                clocked: PhantomData,
                delay: PhantomData,
            },
            eoc,
        })
    }
}

impl<SpiE, PinE, CS, SPI, CLOCKED: Clocked, WAKEUP> Max116xx10Bit<SPI, CS, CLOCKED, WAKEUP>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    #[inline]
    fn send_wrapper(&mut self, byte: u8) -> Result<(), Error<SpiE, PinE>> {
        self.cs.set_low().map_err(Error::Pin)?;
        nb::block!(self.spi.send(byte)).map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        Ok(())
    }

    /// Set up the ADC depending on clock and reference configuration
    #[inline]
    pub fn setup(&mut self) -> Result<(), Error<SpiE, PinE>> {
        self.send_wrapper(self.get_setup_byte())
    }

    /// Set up the Averaging register. This sets the AVGON, NAVG1, NAVG0, NSCAN1 and NSCAN0
    /// bits accordingly
    #[inline]
    pub fn averaging(
        &mut self,
        avg_conv: AveragingConversions,
        avg_res: AveragingResults,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.cfg.results_len = Self::get_results_len(avg_res);
        self.send_wrapper(Self::get_averaging_byte(avg_conv, avg_res))
    }

    #[inline]
    pub fn reset(&mut self, fifo_only: bool) -> Result<(), Error<SpiE, PinE>> {
        let mut reset_byte = 0b0001_0000;
        if fifo_only {
            reset_byte |= 1 << 3;
        }
        self.send_wrapper(reset_byte)
    }

    #[inline]
    pub fn get_setup_byte(&self) -> u8 {
        ((1 << 6) as u8) | ((self.cfg.clk_mode as u8) << 4) | ((self.cfg.ref_mode as u8) << 2)
    }

    #[inline]
    pub fn get_averaging_byte(avg_conv: AveragingConversions, avg_res: AveragingResults) -> u8 {
        ((1 << 5) as u8) | ((avg_conv as u8) << 2) | avg_res as u8
    }

    #[inline]
    pub fn get_results_len(avg_res: AveragingResults) -> u8 {
        (avg_res as u8 + 1) * 4
    }

    #[inline]
    pub fn get_conversion_byte(
        &self,
        scan_mode: ScanMode,
        channel_num: u8,
    ) -> Result<u8, AdcError> {
        if channel_num > self.cfg.max_channels {
            return Err(AdcError::InvalidChannel);
        }
        Ok((1 << 7) | (channel_num << 3) | ((scan_mode as u8) << 1))
    }

    /// Generic function which can be used a single result is available
    /// when EOC is low
    fn internal_read_single_channel<EOC: InputPin<Error = PinE>>(
        &mut self,
        eoc: &mut EOC,
    ) -> nb::Result<u16, Error<SpiE, PinE>> {
        if self.cfg.pending_scan_mode.is_none() {
            return Err(nb::Error::Other(Error::Adc(AdcError::NoPendingOperation)));
        } else if self.cfg.pending_scan_mode != Some(ScanMode::ConvertChannelNOnce) {
            return Err(nb::Error::Other(Error::Adc(AdcError::PendingOperation)));
        }
        if eoc.is_low().map_err(Error::Pin)? {
            let mut dummy_cmd: [u8; 2] = [0; 2];
            self.cs.set_low().map_err(Error::Pin)?;
            let transfer_result = self.spi.transfer(&mut dummy_cmd);
            self.cs.set_high().map_err(Error::Pin)?;
            match transfer_result {
                Ok(reply) => {
                    self.cfg.pending_scan_mode = None;
                    Ok(((reply[0] as u16) << 6) | (reply[1] as u16 >> 2))
                }
                Err(e) => Err(nb::Error::Other(Error::Spi(e))),
            }
        } else {
            Err(nb::Error::WouldBlock)
        }
    }
}

macro_rules! ext_impl {
    () => {
        /// Set up the ADC depending on clock and reference configuration
        #[inline]
        pub fn setup(&mut self) -> Result<(), Error<SpiE, PinE>> {
            self.base.send_wrapper(self.base.get_setup_byte())
        }

        /// Set up the Averaging register. This sets the AVGON, NAVG1, NAVG0, NSCAN1 and NSCAN0
        /// bits accordingly
        #[inline]
        pub fn averaging(
            &mut self,
            avg_conv: AveragingConversions,
            avg_res: AveragingResults,
        ) -> Result<(), Error<SpiE, PinE>> {
            self.base.cfg.results_len = Max116xx10Bit::<SPI, CS, CLOCKED>::get_results_len(avg_res);
            self.base
                .send_wrapper(Max116xx10Bit::<SPI, CS, CLOCKED>::get_averaging_byte(
                    avg_conv, avg_res,
                ))
        }

        #[inline]
        pub fn reset(&mut self, fifo_only: bool) -> Result<(), Error<SpiE, PinE>> {
            let mut reset_byte = 0b0001_0000;
            if fifo_only {
                reset_byte |= 1 << 3;
            }
            self.base.send_wrapper(reset_byte)
        }
    };
}
impl<SpiE, PinE, CS, SPI, EOC, CLOCKED: Clocked> Max116xx10BitEocExt<SPI, CS, EOC, CLOCKED>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    ext_impl!();
}

impl<SpiE, PinE, CS, SPI, EOC, CNVST, CLOCKED: Clocked, DELAY>
    Max116xx10BitCnvstEocExt<SPI, CS, EOC, CNVST, CLOCKED, DELAY>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    ext_impl!();
}

//==================================================================================================
// External SPI clock used
//==================================================================================================

/// Implementations when using the external SPI clock to time the conversions
impl<SpiE, PinE, SPI, CS> Max116xx10Bit<SPI, CS, ExtClkd, WithoutWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    pub fn read_single_channel(
        &mut self,
        buf: &mut [u8],
        channel_num: u8,
    ) -> Result<u16, Error<SpiE, PinE>> {
        if buf.len() < 3 {
            return Err(Error::Adc(AdcError::CmdBufTooSmall));
        }
        buf[0] = self.get_conversion_byte(ScanMode::ConvertChannelNOnce, channel_num)?;
        buf[1] = 0x00;
        buf[2] = 0x00;
        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self.spi.transfer(&mut buf[0..3]).ok().unwrap();
        self.cs.set_high().map_err(Error::Pin)?;
        Ok(((reply[1] as u16) << 6) | (reply[2] as u16 >> 2))
    }

    pub fn read_multiple_channels_0_to_n(
        &mut self,
        buf: &mut [u8],
        result_iter: &mut IterMut<u16>,
        n: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        let mut iter = buf.iter_mut();
        let mut next_byte: &mut u8;
        for idx in 0..n + 1 {
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = self.get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self
            .spi
            .transfer(&mut buf[0..((n + 1) * 2 + 1) as usize])
            .map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        let mut reply_iter = reply.iter();
        // Skip first reply byte
        reply_iter.next().unwrap();
        for _ in 0..n + 1 {
            let next_res = result_iter
                .next()
                .ok_or(Error::Adc(AdcError::ResulBufTooSmall))?;
            *next_res = ((*reply_iter.next().unwrap() as u16) << 6)
                | (*reply_iter.next().unwrap() as u16 >> 2);
        }
        Ok(())
    }

    pub fn read_multiple_channels_n_to_highest(
        &mut self,
        buf: &mut [u8],
        result_iter: &mut IterMut<u16>,
        n: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        let mut iter = buf.iter_mut();
        let mut next_byte: &mut u8;
        if n > self.cfg.max_channels - 1 {
            return Err(Error::Adc(AdcError::InvalidChannel));
        }
        let conversions = self.cfg.max_channels - n;
        for idx in n..self.cfg.max_channels {
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = self.get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self
            .spi
            .transfer(&mut buf[0..(conversions * 2 + 1) as usize])
            .map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        let mut reply_iter = reply.iter();
        // Skip first reply byte
        reply_iter.next().unwrap();
        for _ in 0..conversions {
            let next_res = result_iter
                .next()
                .ok_or(Error::Adc(AdcError::ResulBufTooSmall))?;
            *next_res = ((*reply_iter.next().unwrap() as u16) << 6)
                | (*reply_iter.next().unwrap() as u16 >> 2);
        }
        Ok(())
    }
}

/// Implementations when using the external SPI clock to time the conversions but also requiring
/// a wakeup delay
impl<SpiE, PinE, SPI, CS> Max116xx10Bit<SPI, CS, ExtClkd, WithWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    pub fn read_single_channel<DELAY: DelayUs<u8>>(
        &mut self,
        buf: &mut [u8],
        channel_num: u8,
        delay: &mut DELAY,
    ) -> Result<u16, Error<SpiE, PinE>> {
        if buf.len() < 3 {
            return Err(Error::Adc(AdcError::CmdBufTooSmall));
        }
        buf[0] = self
            .get_conversion_byte(ScanMode::ConvertChannelNOnce, channel_num)
            .map_err(Error::Adc)?;
        self.send_wrapper(buf[0])?;
        delay.delay_us(65);
        buf[0] = 0x00;
        buf[1] = 0x00;
        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self.spi.transfer(&mut buf[0..2]).map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        Ok(((reply[0] as u16) << 6) | (reply[1] as u16 >> 2))
    }

    pub fn read_multiple_channels_0_to_n<DELAY: DelayUs<u8>>(
        &mut self,
        buf: &mut [u8],
        result_iter: &mut IterMut<u16>,
        n: u8,
        delay: &mut DELAY,
    ) -> Result<(), Error<SpiE, PinE>> {
        let mut iter = buf.iter_mut();
        let mut next_byte: &mut u8;
        for idx in 0..n + 1 {
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = self.get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        // Write first conversion byte and then wait 65 us to allow internal reference to power up
        self.send_wrapper(buf[0])?;
        delay.delay_us(65);

        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self
            .spi
            .transfer(&mut buf[1..((n + 1) * 2 + 1) as usize])
            .map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        let mut reply_iter = reply.iter();
        for _ in 0..n + 1 {
            let next_res = result_iter
                .next()
                .ok_or(Error::Adc(AdcError::ResulBufTooSmall))?;
            *next_res = ((*reply_iter.next().unwrap() as u16) << 6)
                | (*reply_iter.next().unwrap() as u16 >> 2);
        }
        Ok(())
    }

    pub fn read_multiple_channels_n_to_highest<DELAY: DelayUs<u8>>(
        &mut self,
        buf: &mut [u8],
        result_iter: &mut IterMut<u16>,
        n: u8,
        delay: &mut DELAY,
    ) -> Result<(), Error<SpiE, PinE>> {
        let mut iter = buf.iter_mut();
        let mut next_byte: &mut u8;
        if n > self.cfg.max_channels - 1 {
            return Err(Error::Adc(AdcError::InvalidChannel));
        }
        let conversions = self.cfg.max_channels - n;
        for idx in n..self.cfg.max_channels {
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = self.get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        // Write first conversion byte and then wait 65 us with CS high to allow internal
        // reference to power up
        self.send_wrapper(buf[0])?;
        delay.delay_us(65);
        self.cs.set_low().map_err(Error::Pin)?;
        let reply = self
            .spi
            .transfer(&mut buf[1..(conversions * 2 + 1) as usize])
            .map_err(Error::Spi)?;
        self.cs.set_high().map_err(Error::Pin)?;
        let mut reply_iter = reply.iter();
        for _ in 0..conversions {
            let next_res = result_iter
                .next()
                .ok_or(Error::Adc(AdcError::ResulBufTooSmall))?;
            *next_res = ((*reply_iter.next().unwrap() as u16) << 6)
                | (*reply_iter.next().unwrap() as u16 >> 2);
        }
        Ok(())
    }
}

//==================================================================================================
// Internal clock, EOC pin used
//==================================================================================================

/// Implementations when using the internal clock with a conversion started
/// through the serial interface
impl<SpiE, PinE, SPI, CS, EOC> Max116xx10BitEocExt<SPI, CS, EOC, IntClkdIntTmdSerIF>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
    EOC: InputPin<Error = PinE>,
{
    #[inline]
    fn request_wrapper(
        &mut self,
        channel_num: u8,
        scan_mode: ScanMode,
    ) -> Result<(), Error<SpiE, PinE>> {
        if self.base.cfg.pending_scan_mode.is_some() {
            return Err(Error::Adc(AdcError::PendingOperation));
        }
        let conv_byte = self
            .base
            .get_conversion_byte(scan_mode, channel_num)
            .map_err(Error::Adc)?;
        self.base.send_wrapper(conv_byte)?;
        self.base.cfg.pending_scan_mode = Some(scan_mode);
        Ok(())
    }

    pub fn request_single_channel(&mut self, channel_num: u8) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(channel_num, ScanMode::ConvertChannelNOnce)
    }

    /// Request a channel repeatedly, using scan mode 10. The number of scans is determined
    /// by the averaging register NSCAN0 and NSCAN1 configuration which can be configured
    /// with the [`averaging`](Max116xx10Bit::averaging) function
    pub fn request_channel_n_repeatedly(
        &mut self,
        channel_num: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(channel_num, ScanMode::ScanChannelNRepeatedly)
    }

    pub fn request_multiple_channels_0_to_n(&mut self, n: u8) -> Result<(), Error<SpiE, PinE>> {
        self.base.cfg.requested_conversions = n as usize + 1;
        self.request_wrapper(n, ScanMode::Scan0ToChannelN)
    }

    pub fn request_multiple_channels_n_to_highest(
        &mut self,
        n: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.base.cfg.requested_conversions = self.base.cfg.max_channels as usize + 1 - n as usize;
        self.request_wrapper(n, ScanMode::ScanChannelNToHighest)
    }

    /// This function is used to retrieve the results for a single byte request. The EOC pin
    /// needs to be passed explicitely here.
    /// If no request was made, [AdcError::NoPendingOperation] is returned.
    /// If a request was made for multipel results, [AdcError::PendingOperation] will be returned.
    pub fn get_single_channel(&mut self) -> nb::Result<u16, Error<SpiE, PinE>> {
        self.base.internal_read_single_channel(&mut self.eoc)
    }

    /// This function is used to retrieve the results for all functions requesting multiple
    /// bytes. If no request was made, [AdcError::NoPendingOperation] is returned.
    /// If a request was made for a single channel, [AdcError::PendingOperation] will be returned.
    pub fn get_multi_channel(
        &mut self,
        result_iter: &mut IterMut<u16>,
    ) -> nb::Result<(), Error<SpiE, PinE>> {
        if self.base.cfg.pending_scan_mode.is_none() {
            return Err(nb::Error::Other(Error::Adc(AdcError::NoPendingOperation)));
        } else if self.base.cfg.pending_scan_mode == Some(ScanMode::ConvertChannelNOnce) {
            return Err(nb::Error::Other(Error::Adc(AdcError::PendingOperation)));
        }
        if self.eoc.is_low().map_err(Error::Pin)? {
            // maximum length of reply is 32 for 16 channels
            let mut dummy_cmd: [u8; 32] = [0; 32];
            let num_conv: usize =
                if self.base.cfg.pending_scan_mode == Some(ScanMode::ScanChannelNRepeatedly) {
                    self.base.cfg.results_len as usize
                } else {
                    self.base.cfg.requested_conversions
                };
            self.base.cfg.pending_scan_mode = None;
            self.base.cfg.requested_conversions = 0;
            self.base.cs.set_low().map_err(Error::Pin)?;
            let transfer_result = self.base.spi.transfer(&mut dummy_cmd[0..(num_conv * 2)]);
            self.base.cs.set_high().map_err(Error::Pin)?;
            match transfer_result {
                Ok(reply) => {
                    let mut reply_iter = reply.iter();
                    for _ in 0..num_conv {
                        let next_res = result_iter
                            .next()
                            .ok_or(Error::Adc(AdcError::ResulBufTooSmall))?;
                        *next_res = ((*reply_iter.next().unwrap() as u16) << 6)
                            | (*reply_iter.next().unwrap() as u16 >> 2);
                    }
                    Ok(())
                }
                Err(e) => Err(nb::Error::Other(Error::Spi(e))),
            }
        } else {
            Err(nb::Error::WouldBlock)
        }
    }
}

//==================================================================================================
// Internal clock, CNVST and EOC pin used
//==================================================================================================

/// Implementations when using the internal clock where CNVST is held low for the duration
/// of the conversion
///
/// TODO: Implement. Unfortunately, the test board used to verify this library did not have
/// the CNVST connected, so I wouldn't be able to test an implementation easily.
impl<SpiE, PinE, SPI, CS, EOC, CNVST>
    Max116xx10BitCnvstEocExt<SPI, CS, EOC, CNVST, IntClkdExtTmdCnvst, WithoutWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
    EOC: InputPin<Error = PinE>,
    CNVST: OutputPin<Error = PinE>,
{
    pub fn dummy() {
        todo!("Implement this")
    }
}

/// Implementations when using the internal clock where CNVST is only pulsed to start acquisition
/// and conversion
///
/// TODO: Test. Unfortunately, the test board used to verify this library did not have
/// the CNVST connected, so I wouldn't be able to test an implementation easily.
impl<SpiE, PinE, SPI, CS, EOC, CNVST>
    Max116xx10BitCnvstEocExt<SPI, CS, EOC, CNVST, IntClkdIntTmdCnvst, WithWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
    EOC: InputPin<Error = PinE>,
    CNVST: OutputPin<Error = PinE>,
{
    /// The pulse needs to be at least 40ns. A pulse cycle value can be used to increase
    /// the width of the pulse
    pub fn request_single_channel(
        &mut self,
        channel_num: u8,
        pulse_cycles: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(channel_num, ScanMode::ConvertChannelNOnce, pulse_cycles)
    }

    #[inline]
    fn request_wrapper(
        &mut self,
        channel_num: u8,
        scan_mode: ScanMode,
        pulse_cycles: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        if self.base.cfg.pending_scan_mode.is_some() {
            return Err(Error::Adc(AdcError::PendingOperation));
        }
        let conv_byte = self
            .base
            .get_conversion_byte(scan_mode, channel_num)
            .map_err(Error::Adc)?;
        self.base.send_wrapper(conv_byte)?;
        self.cnvst.set_low().map_err(Error::Pin)?;
        for _ in 0..pulse_cycles {}
        self.cnvst.set_high().map_err(Error::Pin)?;
        self.base.cfg.pending_scan_mode = Some(scan_mode);
        Ok(())
    }

    pub fn get_single_channel(&mut self) -> nb::Result<u16, Error<SpiE, PinE>> {
        self.base.internal_read_single_channel(&mut self.eoc)
    }
}

mod private {
    pub trait Sealed {}
}
