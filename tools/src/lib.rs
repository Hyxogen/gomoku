use std::fmt;
use std::str;
use std::ops::{Add, Neg, Sub};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct DeltaPos(i8, i8);

impl DeltaPos { 
    pub const ZERO: DeltaPos = Self::new(0, 0);

    pub const fn new(drow: i8, dcol: i8) -> Self {
        Self { 0: drow, 1: dcol }
    }

    pub const fn drow(&self) -> i8 {
        self.0
    }

    pub const fn dcol(&self) -> i8 {
        self.1
    }
}

impl Neg for DeltaPos {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            0: -self.0,
            1: -self.1,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Pos(u8, u8);

impl Pos {
    pub const fn new(row: u8, col: u8) -> Self {
        Self { 0: row, 1: col }
    }

    pub const fn row(&self) -> u8 {
        self.0
    }

    pub const fn col(&self) -> u8 {
        self.1
    }

    pub const fn transpose(self) -> Self {
        Pos::new(self.col(), self.row())
    }
}

impl Add<DeltaPos> for Pos {
    type Output = Self;

    fn add(self, rhs: DeltaPos) -> Self::Output {
        Pos::new((self.row() as i8 + rhs.drow()) as u8, (self.col() as i8 + rhs.dcol()) as u8)
    }
}

impl Sub<DeltaPos> for Pos {
    type Output = Self;

    fn sub(self, rhs: DeltaPos) -> Self::Output {
        self + -rhs
    }
}

impl<T, U> From<(T, U)> for DeltaPos
where
    T: Into<i8>,
    U: Into<i8>,
{
    fn from(value: (T, U)) -> Self {
        Self::new(value.0.into(), value.1.into())
    }
}

impl<T, U> From<(T, U)> for Pos
where
    T: Into<u8>,
    U: Into<u8>,
{
    fn from(value: (T, U)) -> Self {
        Self::new(value.0.into(), value.1.into())
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_assert!(self.row() < 26);
        write!(f, "{}{}", (self.col() + 'a' as u8) as char, self.row() + 1)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ParsePosError {
    NoColumn,
    NotAscii,
    NoDigits,
    TooLarge,
    InvalidNum,
    IsZero,
}

impl fmt::Display for ParsePosError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoColumn => write!(f, "no column specified"),
            Self::NotAscii => write!(f, "found non-ascii character"),
            Self::NoDigits => write!(f, "expected digits"),
            Self::TooLarge => write!(f, "number too large"),
            Self::InvalidNum => write!(f, "expected a number"),
            Self::IsZero => write!(f, "number may not be zero"),
        }
    }
}

impl std::error::Error for ParsePosError {}

impl str::FromStr for Pos {
    type Err = ParsePosError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.chars();

        let ch = iter.next().ok_or(ParsePosError::NoColumn)?;
        if !ch.is_ascii_alphabetic() {
            return Err(ParsePosError::NotAscii);
        }

        let col = ch.to_ascii_lowercase() as u8 - 'a' as u8;

        let mut got_digit = false;
        let mut row: u8 = 0;

        while let Some(digit) = iter.next().and_then(|x| x.to_digit(10)) {
            row = row.checked_mul(10).ok_or(ParsePosError::TooLarge)?;
            row = row
                .checked_add(digit as u8)
                .ok_or(ParsePosError::TooLarge)?;

            got_digit = true;
        }

        if !got_digit {
            Err(ParsePosError::NoDigits)
        } else if iter.next() != None {
            Err(ParsePosError::InvalidNum)
        } else if row == 0 {
            Err(ParsePosError::IsZero)
        } else {
            Ok(Pos::new(row - 1, col))
        }
    }
}
