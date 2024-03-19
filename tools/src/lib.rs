use std::fmt;
use std::str;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Pos(usize, usize);

impl Pos {
    pub const fn new(row: usize, col: usize) -> Self {
        Self { 0: row, 1: col }
    }

    pub const fn row(&self) -> usize {
        self.0
    }

    pub const fn col(&self) -> usize {
        self.1
    }

    pub const fn transpose(self) -> Self {
        Pos::new(self.col(), self.row())
    }
}

impl<T> From<(T, T)> for Pos
where
    T: Into<usize>,
{
    fn from(value: (T, T)) -> Self {
        Self::new(value.0.into(), value.1.into())
    }
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_assert!(self.row() < 26);
        write!(
            f,
            "{}{}",
            (self.col() + ('a' as usize)) as u8 as char,
            self.row() + 1
        )
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

        let col = ch.to_ascii_lowercase() as usize - 'a' as usize;

        let mut got_digit = false;
        let mut row: usize = 0;

        while let Some(digit) = iter.next().and_then(|x| x.to_digit(10)) {
            row = row.checked_mul(10).ok_or(ParsePosError::TooLarge)?;
            row = row
                .checked_add(digit as usize)
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
