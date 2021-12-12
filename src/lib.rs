#![no_std]
use core::{marker::PhantomData, slice::IterMut};
use embedded_hal::{
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

pub struct Max11618;
pub struct Max11619;
pub struct Max11620;
pub struct Max11621;
pub struct Max11624;
pub struct Max11625;

pub struct WithWakeupDelay;
pub struct WithoutWakeupDelay;

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

pub struct InternallyClockedExternallyTimedCnvst {}
impl private::Sealed for InternallyClockedExternallyTimedCnvst {}
impl Clocked for InternallyClockedExternallyTimedCnvst {
    const CLK_SEL: ClockMode = ClockMode::InternalClockExternallyTimedCnvst;
}
impl InternallyClocked for InternallyClockedExternallyTimedCnvst {}

pub struct InternallyClockedInternallyTimedSerialInterface {}
impl private::Sealed for InternallyClockedInternallyTimedSerialInterface {}
impl Clocked for InternallyClockedInternallyTimedSerialInterface {
    const CLK_SEL: ClockMode = ClockMode::InternalClockInternallyTimedSerialInterface;
}
impl InternallyClocked for InternallyClockedInternallyTimedSerialInterface {}

pub struct ExternallyClocked {}
impl private::Sealed for ExternallyClocked {}
impl Clocked for ExternallyClocked {
    const CLK_SEL: ClockMode = ClockMode::ExternalClockExternallyTimedSclk;
}

//==================================================================================================
// Definitions
//==================================================================================================

#[derive(Debug, PartialEq)]
pub enum PendingOp {
    None,
    SingleChannel,
    MultiChannel,
}

/// Clock modes for the MAX116XX devices
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum ClockMode {
    /// CNVST Configuration: CNVST active low
    InternalClockInternallyTimedCnvst = 0b00,
    /// Externally timed through CNVST. CNVST Configuration: CNVST active low
    InternalClockExternallyTimedCnvst = 0b01,
    /// Default mode at power-up. CNVST Configuration: AIN15/AIN11/AIN7
    /// Start conversions using the serial interface instead of CNVST
    InternalClockInternallyTimedSerialInterface = 0b10,
    ExternalClockExternallyTimedSclk = 0b11,
}

/// Voltage reference modes
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum RefMode {
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
pub enum AveragingResults {
    FourResults = 0b00,
    EightResults = 0b01,
    TwelveResults = 0b10,
    SixteenResults = 0b11,
}

pub enum ScanMode {
    Scan0ToChannelN = 0b00,
    ScanChannelNToHighest = 0b01,
    ScanChnanelNRepeatedly = 0b10,
    ConvertChannelNOnce = 0b11,
}

#[derive(Debug)]
pub enum AdcError {
    InvalidChannel,
    CmdBufTooSmall,
    ResulBufTooSmall,
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

//==================================================================================================
// ADc implementation
//==================================================================================================

pub struct Max116xx10Bit<
    SPI,
    CS,
    MAX: HasChannels,
    CLOCKED = ExternallyClocked,
    DELAY = WithoutWakeupDelay,
> {
    clk_mode: ClockMode,
    ref_mode: RefMode,
    spi: SPI,
    cs: CS,
    pending_op: PendingOp,
    max: PhantomData<MAX>,
    clocked: PhantomData<CLOCKED>,
    delay: PhantomData<DELAY>,
}

impl<SpiE, PinE, CS, SPI, MAX: HasChannels, CLOCKED: Clocked, DELAY>
    Max116xx10Bit<SPI, CS, MAX, CLOCKED, DELAY>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    /// Create a new generic MAX116xx instance.
    pub fn new(spi: SPI, cs: CS, ref_mode: RefMode) -> Result<Self, Error<SpiE, PinE>> {
        let mut max_dev = Max116xx10Bit {
            clk_mode: CLOCKED::CLK_SEL,
            ref_mode,
            spi,
            cs,
            pending_op: PendingOp::None,
            max: PhantomData,
            delay: PhantomData,
            clocked: PhantomData,
        };
        max_dev.setup()?;
        Ok(max_dev)
    }

    #[inline]
    fn send_wrapper(&mut self, byte: u8) -> Result<(), Error<SpiE, PinE>> {
        self.cs.set_low().map_err(|e| Error::Pin(e))?;
        nb::block!(self.spi.send(byte)).map_err(|e| Error::Spi(e))?;
        self.cs.set_high().map_err(|e| Error::Pin(e))?;
        Ok(())
    }

    #[inline]
    pub fn setup(&mut self) -> Result<(), Error<SpiE, PinE>> {
        self.send_wrapper(self.get_setup_byte())
    }

    #[inline]
    pub fn averaging(
        &mut self,
        avg_conv: AveragingConversions,
        avg_res: AveragingResults,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.send_wrapper(Self::get_averaging_byte(avg_conv, avg_res))
    }

    #[inline]
    pub fn reset_adc(&mut self, fifo_only: bool) -> Result<(), Error<SpiE, PinE>> {
        let mut reset_byte = 0b0001_0000;
        if fifo_only {
            reset_byte |= 1 << 3;
        }
        self.send_wrapper(reset_byte)
    }

    #[inline]
    pub fn get_setup_byte(&self) -> u8 {
        ((1 << 6) as u8) | ((self.clk_mode as u8) << 4) | ((self.ref_mode as u8) << 2)
    }

    #[inline]
    pub fn get_averaging_byte(avg_conv: AveragingConversions, avg_res: AveragingResults) -> u8 {
        ((1 << 5) as u8) | ((avg_conv as u8) << 2) | avg_res as u8
    }

    #[inline]
    pub fn get_conversion_byte(scan_mode: ScanMode, channel_num: u8) -> Result<u8, AdcError> {
        if channel_num > MAX::NUM {
            return Err(AdcError::InvalidChannel);
        }
        Ok((1 << 7) | (channel_num << 3) | ((scan_mode as u8) << 1))
    }
}
impl<SpiE, PinE, SPI, CS, MAX: HasChannels>
    Max116xx10Bit<SPI, CS, MAX, InternallyClockedInternallyTimedSerialInterface, WithoutWakeupDelay>
where
    SPI: Transfer<u8, Error = SpiE> + FullDuplex<u8, Error = SpiE>,
    CS: OutputPin<Error = PinE>,
{
    #[inline]
    fn request_wrapper(
        &mut self,
        channel_num: u8,
        scan_mode: ScanMode,
        op_type: PendingOp,
    ) -> Result<(), Error<SpiE, PinE>> {
        if self.pending_op != PendingOp::None {
            return Err(Error::Adc(AdcError::PendingOperation));
        }
        let conv_byte =
            Self::get_conversion_byte(scan_mode, channel_num).map_err(|e| Error::Adc(e))?;
        self.send_wrapper(conv_byte)?;
        self.pending_op = op_type;
        Ok(())
    }

    pub fn request_single_channel(&mut self, channel_num: u8) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(
            channel_num,
            ScanMode::ConvertChannelNOnce,
            PendingOp::SingleChannel,
        )
    }

    pub fn request_multiple_channels_0_to_n(&mut self, n: u8) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(n, ScanMode::Scan0ToChannelN, PendingOp::MultiChannel)
    }

    pub fn request_multiple_channels_n_to_highest(
        &mut self,
        n: u8,
    ) -> Result<(), Error<SpiE, PinE>> {
        self.request_wrapper(n, ScanMode::ScanChannelNToHighest, PendingOp::MultiChannel)
    }

    pub fn get_single_channel<I: InputPin<Error = PinE>>(
        &mut self,
        eoc_pin: &mut I,
    ) -> nb::Result<u16, Error<SpiE, PinE>> {
        if self.pending_op != PendingOp::SingleChannel {
            return Err(nb::Error::Other(Error::Adc(AdcError::NoPendingOperation)));
        }
        let is_low = match eoc_pin.is_low() {
            Ok(low) => low,
            Err(e) => {
                return Err(nb::Error::Other(Error::Pin(e)));
            }
        };
        if is_low {
            let mut dummy_cmd: [u8; 2] = [0; 2];
            self.cs.set_low().map_err(|e| Error::Pin(e))?;
            let transfer_result =  self.spi.transfer(&mut dummy_cmd);
            self.cs.set_high().map_err(|e| Error::Pin(e))?;
            match transfer_result {
                Ok(reply) => {
                    self.pending_op = PendingOp::None;
                    Ok(((reply[0] as u16) << 6) | (reply[1] as u16 >> 2))
                }
                Err(e) => Err(nb::Error::Other(Error::Spi(e))),
            }
        } else {
            Err(nb::Error::WouldBlock)
        }
    }
}

impl<SpiE, PinE, SPI, CS, MAX: HasChannels>
    Max116xx10Bit<SPI, CS, MAX, ExternallyClocked, WithoutWakeupDelay>
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

        match Self::get_conversion_byte(ScanMode::ConvertChannelNOnce, channel_num) {
            Ok(byte) => buf[0] = byte,
            Err(e) => {
                return Err(Error::Adc(e));
            }
        };
        buf[1] = 0x00;
        buf[2] = 0x00;
        self.cs.set_low().map_err(|e| Error::Pin(e))?;
        let reply = self.spi.transfer(&mut buf[0..3]).ok().unwrap();
        self.cs.set_high().map_err(|e| Error::Pin(e))?;
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
            *next_byte = Self::get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        self.cs.set_low().map_err(|e| Error::Pin(e))?;
        let reply = self
            .spi
            .transfer(&mut buf[0..((n + 1) * 2 + 1) as usize])
            .map_err(|e| Error::Spi(e))?;
        self.cs.set_high().map_err(|e| Error::Pin(e))?;
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
        if n > MAX::NUM - 1 {
            return Err(Error::Adc(AdcError::InvalidChannel));
        }
        let conversions = MAX::NUM - n;
        for idx in n..MAX::NUM {
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = Self::get_conversion_byte(ScanMode::ConvertChannelNOnce, idx)?;
            next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
            *next_byte = 0x00;
        }
        next_byte = iter.next().ok_or(Error::Adc(AdcError::CmdBufTooSmall))?;
        *next_byte = 0x00;
        self.cs.set_low().map_err(|e| Error::Pin(e))?;
        let reply = self
            .spi
            .transfer(&mut buf[0..(conversions * 2 + 1) as usize])
            .map_err(|e| Error::Spi(e))?;
        self.cs.set_high().map_err(|e| Error::Pin(e))?;
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

mod private {
    pub trait Sealed {}
}
