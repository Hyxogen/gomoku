use crate::table::*;
use anyhow::{bail, Error};
#[cfg(test)]
use std::collections::HashMap;
use std::fmt;
use std::ops::{BitXor, Not};
use std::str::FromStr;
use tools::Pos;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BitBoard<const SIZE: usize> {
    rows: [u64; SIZE],
}

impl<const SIZE: usize> fmt::Debug for BitBoard<SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in 0..(SIZE as u8) {
            for col in 0..64 {
                if self.at((row, col).into()) {
                    write!(f, "1")?;
                } else {
                    write!(f, "0")?;
                }
                write!(f, " ")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

pub const fn get_bit(string: u64, idx: u8) -> bool {
    debug_assert!(idx < 64);
    (string & (1 << idx)) != 0
}

pub const fn set_bit(string: u64, idx: u8, val: bool) -> u64 {
    debug_assert!(idx < 64);
    let mask = 1 << idx;
    let b = if val { mask } else { 0 };

    (string & !mask) | b
}

impl<const SIZE: usize> BitBoard<SIZE> {
    pub const fn new() -> Self {
        Self::from_row(0)
    }

    pub const fn from_row(row: u64) -> Self {
        Self { rows: [row; SIZE] }
    }

    pub const fn filled() -> Self {
        Self::from_row(u64::MAX)
    }

    pub const fn not(mut self) -> Self {
        let mut i = 0;

        while i < SIZE {
            self.rows[i] = !self.rows[i];
            i += 1;
        }
        self
    }

    pub const fn row(&self, row: u8) -> u64 {
        self.rows[row as usize]
    }

    pub const fn at(&self, pos: Pos) -> bool {
        debug_assert!((pos.col() as usize) < 64);
        get_bit(self.row(pos.row()), pos.col())
    }

    pub const fn set(mut self, pos: Pos, val: bool) -> Self {
        debug_assert!((pos.col() as usize) < 64);
        self.rows[pos.row() as usize] = set_bit(self.rows[pos.row() as usize], pos.col(), val);
        self
    }

    pub fn is_empty(&self) -> bool {
        self.rows.iter().all(|row| *row == 0)
    }
}

impl<const SIZE: usize> Default for BitBoard<SIZE> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const SIZE: usize> BitXor for BitBoard<SIZE> {
    type Output = Self;

    fn bitxor(mut self, rhs: Self) -> Self::Output {
        for i in 0..SIZE {
            self.rows[i] ^= rhs.rows[i];
        }
        self
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Side {
    Black,
    White,
}

impl Not for Side {
    type Output = Side;

    fn not(self) -> Self::Output {
        self.opposite()
    }
}

impl Side {
    pub const fn opposite(self) -> Self {
        match self {
            Self::White => Self::Black,
            Self::Black => Self::White,
        }
    }
}

#[derive(Copy, Clone, Debug, Ord, PartialOrd)]
pub enum Three<T> {
    Straight(T, T),
    Normal(T),
}

impl<T> PartialEq for Three<T>
where
    T: PartialEq<T>,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Normal(a), Self::Normal(b)) => a == b,
            (Self::Straight(a1, a2), Self::Straight(b1, b2)) => {
                (a1 == b1 && a2 == b2) || (a1 == b2 && a2 == b1)
            }
            _ => false,
        }
    }
}

impl<T> Eq for Three<T> where T: PartialEq<T> {}

impl Three<u8> {
    pub const fn add(self, v: u8) -> Self {
        match self {
            Self::Straight(a, b) => Self::Straight(a + v, b + v),
            Self::Normal(a) => Self::Normal(a + v),
        }
    }
}

impl<T> Three<T> {
    pub fn map<F>(self, f: F) -> Self
    where
        F: Fn(T) -> T,
    {
        match self {
            Self::Normal(a) => Self::Normal(f(a)),
            Self::Straight(a, b) => Self::Straight(f(a), f(b)),
        }
    }
}

pub struct ThreeIter<T> {
    inner: Three<T>,
    idx: u8,
}

impl<T: Copy> ThreeIter<T> {
    pub const fn new(inner: Three<T>) -> Self {
        Self { inner, idx: 0 }
    }
}

impl<T: Copy> Iterator for ThreeIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner {
            Three::Normal(a) if self.idx == 0 => {
                self.idx += 1;
                Some(a)
            }
            Three::Straight(a, _) if self.idx == 0 => {
                self.idx += 1;
                Some(a)
            }
            Three::Straight(_, b) if self.idx == 1 => {
                self.idx += 1;
                Some(b)
            }
            _ => None,
        }
    }
}

impl<T: Copy> IntoIterator for Three<T> {
    type Item = <ThreeIter<T> as Iterator>::Item;
    type IntoIter = ThreeIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        ThreeIter::new(self)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum Four<T> {
    Normal(T),
    Straight(T, T),
    Double(T, T),
}

impl<T> PartialEq for Four<T>
where
    T: PartialEq<T>,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Normal(a), Self::Normal(b)) => a == b,
            (Self::Straight(a1, a2), Self::Straight(b1, b2))
            | (Self::Double(a1, a2), Self::Double(b1, b2)) => {
                (a1 == b1 && a2 == b2) || (a1 == b2 && a2 == b1)
            }
            _ => false,
        }
    }
}

impl<T> Eq for Four<T> where T: PartialEq<T> {}

impl Four<u8> {
    pub const fn add(self, v: u8) -> Self {
        match self {
            Self::Straight(a, b) => Self::Straight(a + v, b + v),
            Self::Double(a, b) => Self::Double(a + v, b + v),
            Self::Normal(a) => Self::Normal(a + v),
        }
    }
}

impl<T> Four<T> {
    pub fn map<F>(self, f: F) -> Self
    where
        F: Fn(T) -> T,
    {
        match self {
            Self::Normal(a) => Self::Normal(f(a)),
            Self::Straight(a, b) => Self::Straight(f(a), f(b)),
            Self::Double(a, b) => Self::Double(f(a), f(b)),
        }
    }
}

pub struct FourIter<T> {
    inner: Four<T>,
    idx: u8,
}

impl<T: Copy> FourIter<T> {
    pub const fn new(inner: Four<T>) -> Self {
        Self { inner, idx: 0 }
    }
}

impl<T: Copy> Iterator for FourIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner {
            Four::Normal(a) if self.idx == 0 => {
                self.idx += 1;
                Some(a)
            }
            Four::Straight(a, _) | Four::Double(a, _) if self.idx == 0 => {
                self.idx += 1;
                Some(a)
            }
            Four::Straight(_, b) | Four::Double(_, b) if self.idx == 1 => {
                self.idx += 1;
                Some(b)
            }
            _ => None,
        }
    }
}

impl<T: Copy> IntoIterator for Four<T> {
    type Item = <FourIter<T> as Iterator>::Item;
    type IntoIter = FourIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        FourIter::new(self)
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PieceBoard<const SIZE: usize> {
    pieces: BitBoard<SIZE>,
    black: BitBoard<SIZE>,
}

impl<const SIZE: usize> fmt::Debug for PieceBoard<SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "    ")?;
        for col in 0..SIZE {
            if col < 10 {
                write!(f, "{}", (col as u8 + b'0') as char)?;
            } else {
                write!(f, "{}", ((col - 10) as u8 + b'a') as char)?;
            }
            write!(f, " ")?;
        }
        writeln!(f)?;

        for row in 0..Self::SIZEU8 {
            write!(f, "{:0>2}) ", row)?;
            for col in 0..64 {
                match self.at(Pos::new(row, col)) {
                    None => write!(f, ".")?,
                    Some(Side::Black) => write!(f, "b")?,
                    Some(Side::White) => write!(f, "w")?,
                }
                write!(f, " ")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<const SIZE: usize> PieceBoard<SIZE> {
    pub const SIZEU8: u8 = SIZE as u8;

    const NORMAL_BOUNDARY_BOARD: BitBoard<RENJU_BOARD_SIZE> = Board::normal_boundary_board();
    const DIAGONAL_BOUNDARY_BOARD: BitBoard<RENJU_DIAG_BOARD_SIZE> = Board::diag_boundary_board();

    pub const fn new() -> Self {
        Self {
            pieces: BitBoard::new(),
            black: BitBoard::new(),
        }
    }

    pub const fn at(&self, pos: Pos) -> Option<Side> {
        let has_piece = self.pieces.at(pos);
        let is_black = self.black.at(pos);

        debug_assert!(!(is_black && !has_piece));
        match (has_piece, is_black) {
            (true, true) => Some(Side::Black),
            (true, false) => Some(Side::White),
            _ => None,
        }
    }

    const fn black(&self) -> &BitBoard<SIZE> {
        &self.black
    }

    const fn is_black(v: Option<Side>) -> bool {
        matches!(v, Some(Side::Black))
    }

    pub const fn set(mut self, pos: Pos, val: Option<Side>) -> Self {
        self.pieces = self.pieces.set(pos, val.is_some());
        self.black = self.black.set(pos, Self::is_black(val));
        self
    }

    const fn row_of(&self, row: u8, side: Side) -> u64 {
        match side {
            Side::Black => self.black.row(row),
            Side::White => self.pieces.row(row) ^ self.black.row(row),
        }
    }

    // All three patterns:
    // b = black
    // . = no piece (must NOT be border)
    // x = no black (may be a border)
    // , = anything (may be border)
    //
    // Definition:
    // A row with three stones to which you, without at the same time a five in a row is
    // made, can add one more stone to attain a straight four.
    //
    // A straight four must look like this (at least for black in renju rules):
    // x.bbbb.x
    //
    // So a three misses one of these black stones:
    //
    // x..bbb.x
    // x.b.bb.x
    // x.bb.b.x
    // x.bbb..x
    //
    // mask
    //      V
    // x..bbb.x,,,
    // ,,,x.b.bb.x
    // ,,,x.bbb..x
    // x.bb.b.x,,,
    // 11111111111
    //
    // 15 patterns in total:
    //
    // Straight:
    //      v
    // x..bbb..x,,
    // ,x..bbb..x,
    // ,,x..bbb..x
    //      v
    // ,,x..bbb..x
    // ,x..bbb..x,
    // x..bbb..x,,
    //
    // (These two patterns are the same)
    //
    // Normal:
    //      V
    // x..bbb.x,,,
    // ,x..bbb.x,,
    // ,,x..bbb.x,
    //      V
    // ,,,x.b.bb.x
    // ,x.b.bb.x,,
    // x.b.bb.x,,,
    //      V
    // ,,,x.bbb..x
    // ,,x.bbb..x,
    // ,x.bbb..x,,
    //      V
    // x.bb.b.x,,,
    // ,,x.bb.b.x,
    // ,,,x.bb.b.x
    //
    // For each pattern, there are exactly three places for black stones to be placed
    fn get_three_impl(idx: u8, our_row: u64, their_row: u64, border_row: u64) -> Option<Three<u8>> {
        const MASK: u64 = 0b11111111111;

        debug_assert!(idx >= 11);
        let offset = idx - 5;
        let our_row = ((our_row >> offset) & MASK) as u16;
        let their_row = ((their_row >> offset) & MASK) as u16;
        let border_row = ((border_row >> offset) & MASK) as u16;

        const THREE_PATTERNS: &[u16] = &[
            0b00011100000,
            0b00001110000,
            0b00000111000,
            0b00011100000,
            0b00001110000,
            0b00000111000,
            0b00000101100,
            0b00010110000,
            0b00101100000,
            0b00000111000,
            0b00001110000,
            0b00011100000,
            0b00110100000,
            0b00001101000,
            0b00000110100,
        ];

        const EMPTY_PATTERNS: &[u16] = &[
            0b01100011000,
            0b00110001100,
            0b00011000110,
            0b01100010000,
            0b00110001000,
            0b00011000100,
            0b00001010010,
            0b00101001000,
            0b01010010000,
            0b00001000110,
            0b00010001100,
            0b00100011000,
            0b01001010000,
            0b00010010100,
            0b00001001010,
        ];

        const NO_OURS_PATTERNS: &[u16] = &[
            0b10000000100,
            0b01000000010,
            0b00100000001,
            0b10000001000,
            0b01000000100,
            0b00100000010,
            0b00010000001,
            0b01000000100,
            0b10000001000,
            0b00010000001,
            0b00100000010,
            0b01000000100,
            0b10000001000,
            0b00100000010,
            0b00010000001,
        ];

        const FOUR_OFFSETS: &[Three<u8>] = &[
            Three::Straight(4, 8),
            Three::Straight(3, 7),
            Three::Straight(2, 6),
            Three::Normal(8),
            Three::Normal(7),
            Three::Normal(6),
            Three::Normal(4),
            Three::Normal(6),
            Three::Normal(7),
            Three::Normal(2),
            Three::Normal(3),
            Three::Normal(4),
            Three::Normal(6),
            Three::Normal(4),
            Three::Normal(3),
        ];

        let mut i = 0;
        while i < THREE_PATTERNS.len() {
            if (our_row & THREE_PATTERNS[i]) == THREE_PATTERNS[i]
                && (their_row & EMPTY_PATTERNS[i]) == 0
                && (our_row & EMPTY_PATTERNS[i]) == 0
                && (border_row & EMPTY_PATTERNS[i]) == 0
                && (our_row & NO_OURS_PATTERNS[i]) == 0
            {
                return Some(FOUR_OFFSETS[i].add(offset));
            }
            i += 1;
        }

        None
    }

    pub fn get_three(&self, pos: Pos, side: Side) -> Option<Three<Pos>> {
        let our_row = self.row_of(pos.row(), side);
        let their_row = self.row_of(pos.row(), side.opposite());
        let border_row = if SIZE == RENJU_BOARD_SIZE {
            Self::NORMAL_BOUNDARY_BOARD.row(pos.row())
        } else {
            Self::DIAGONAL_BOUNDARY_BOARD.row(pos.row())
        };

        match Self::get_three_impl(pos.col(), our_row, their_row, border_row) {
            Some(Three::Normal(col)) => Some(Three::Normal(Pos::new(pos.row(), col))),
            Some(Three::Straight(col1, col2)) => Some(Three::Straight(
                Pos::new(pos.row(), col1),
                Pos::new(pos.row(), col2),
            )),
            _ => None,
        }
    }

    // Straight Four Definition:
    // An unbroken row with four stones ("four") to which you, in two different ways,
    // can add one more stone to attain five in a row.
    //
    // Four Definition:
    // A row with four stones to which you can add one more stone to attain five in a row.
    //
    // All four patterns:
    // b = black
    // . = no piece (must NOT be border)
    // x = no black (may be a border)
    // , = anything (may be border)
    //
    // Straight (exactly two intersections to make a five):
    // x.bbbb.x
    //
    // Normal (only one intersection to make a five):
    // x.bbbbx
    // xb.bbbx
    // xbb.bbx
    // xbbb.bx
    // xbbbb.x
    //
    // Degenerate (exactly two intersections to make a five):
    // xb.bbb.bx
    //
    // Degenerate patterns:
    //      V
    // ,,xb.bbb.bx
    // ,xb.bbb.bx,
    // xb.bbb.bx,,
    //      V
    // xbb.bb.bbx,
    // ,xbb.bb.bbx
    //      V
    // xbbb.b.bbbx
    //
    // NOTE: THESE POSITIONS ARE NOT DEGENERATE
    //  V     V     V
    // xb.bbb.bx,,,,,
    // ,,,,,,xb.bbb.bx
    //
    // Rather they're just a normal pattern
    //
    // Straight patterns:
    //      V
    // ,,,x.bbbb.x
    // ,,x.bbbb.x,
    // ,x.bbbb.x,,
    // x.bbbb.x,,,
    //
    // Normal patterns:
    //      V
    // ,,,,xbbbb.x
    // ,,,xbbbb.x,
    // ,,xbbbb.x,,
    // ,xbbbb.x,,,
    //      V
    // ,,,,xb.bbbx
    // ,,xb.bbbx,,
    // ,xb.bbbx,,,
    // xb.bbbx,,,,
    //      V
    // ,,,,xbb.bbx
    // ,,,xbb.bbx,
    // ,xbb.bbx,,,
    // xbb.bbx,,,,
    //      V
    // ,,,,xbbb.bx
    // ,,,xbbb.bx,
    // ,,xbbb.bx,,
    // xbbb.bx,,,,
    //      V
    // ,,,x.bbbbx,
    // ,,x.bbbbx,,
    // ,x.bbbbx,,,
    // x.bbbbx,,,,
    fn get_four_impl(idx: u8, our_row: u64, their_row: u64, border_row: u64) -> Option<Four<u8>> {
        const MASK: u64 = (1 << 11) - 1;
        debug_assert!(idx >= 11);

        let offset = idx - 5;
        let our_row = ((our_row >> offset) & MASK) as u16;
        let their_row = ((their_row >> offset) & MASK) as u16;
        let border_row = ((border_row >> offset) & MASK) as u16;

        // NOTE: The normal patterns can also be done by flipping the bitstring and checking for
        // the first one
        //
        // In other words, we could probably save space by checking for patterns inversed:
        // ,,,xbbbb.x,,,,,
        // Is the inversed version of:
        // ,,,,,x.bbbbx,,,

        const FOUR_PATTERNS: &[u16] = &[
            //Degenerate
            0b00010111010, // ,,xb.bbb.bx
            0b00101110100, // ,xb.bbb.bx,
            0b01011101000, // xb.bbb.bx,,
            //
            0b01101101100, // xbb.bb.bbx,
            0b00110110110, // ,xbb.bb.bbx
            //
            0b01110101110, // xbbb.b.bbbx
            //Straight
            0b00000111100, // ,,,x.bbbb.x
            0b00001111000, // ,,x.bbbb.x,
            0b00011110000, // ,x.bbbb.x,,
            0b00111100000, // x.bbbb.x,,,
            //Normal
            0b00000111100, // ,,,,xbbbb.x
            0b00001111000, // ,,,xbbbb.x,
            0b00011110000, // ,,xbbbb.x,,
            0b00111100000, // ,xbbbb.x,,,
            //
            0b00000101110, // ,,,,xb.bbbx
            0b00010111000, // ,,xb.bbbx,,
            0b00101110000, // ,xb.bbbx,,,
            0b01011100000, // xb.bbbx,,,,
            //
            0b00000110110, // ,,,,xbb.bbx
            0b00001101100, // ,,,xbb.bbx,
            0b00110110000, // ,xbb.bbx,,,
            0b01101100000, // xbb.bbx,,,,
            //
            0b00000111010, // ,,,,xbbb.bx
            0b00001110100, // ,,,xbbb.bx,
            0b00011101000, // ,,xbbb.bx,,
            0b01110100000, // xbbb.bx,,,,
            //
            0b00000111100, // ,,,x.bbbbx,
            0b00001111000, // ,,x.bbbbx,,
            0b00011110000, // ,x.bbbbx,,,
            0b00111100000, // x.bbbbx,,,,
        ];

        const EMPTY_PATTERNS: &[u16] = &[
            //Degenerate
            0b00001000100,
            0b00010001000,
            0b00100010000,
            //
            0b00010010000,
            0b00001001000,
            //
            0b00001010000,
            //Straight
            0b00001000010,
            0b00010000100,
            0b00100001000,
            0b01000010000,
            //Normal
            0b00000000010,
            0b00000000100,
            0b00000001000,
            0b00000010000,
            //
            0b00000010000,
            0b00001000000,
            0b00010000000,
            0b00100000000,
            //
            0b00000001000,
            0b00000010000,
            0b00001000000,
            0b00010000000,
            //
            0b00000000100,
            0b00000001000,
            0b00000010000,
            0b00001000000,
            //
            0b00001000000,
            0b00010000000,
            0b00100000000,
            0b01000000000,
        ];

        const NO_OURS_PATTERNS: &[u16] = &[
            //Degenerate
            0b00100000001,
            0b01000000010,
            0b10000000100,
            //
            0b10000000010,
            0b01000000001,
            //
            0b10000000001,
            //Straight
            0b00010000001,
            0b00100000010,
            0b01000000100,
            0b10000001000,
            //Normal
            0b00001000001,
            0b00010000010,
            0b00100000100,
            0b01000001000,
            //
            0b00001000001,
            0b00100000100,
            0b01000001000,
            0b10000010000,
            //
            0b00001000001,
            0b00010000010,
            0b01000001000,
            0b10000010000,
            //
            0b00001000001,
            0b00010000010,
            0b00100000100,
            0b10000010000,
            //
            0b00010000010,
            0b00100000100,
            0b01000001000,
            0b10000010000,
        ];

        const FIVE_OFFSETS: &[Four<u8>] = &[
            // ,,xb.bbb.bx
            // ,xb.bbb.bx,
            // xb.bbb.bx,,
            Four::Double(2, 6),
            Four::Double(3, 7),
            Four::Double(4, 8),
            // xbb.bb.bbx,
            // ,xbb.bb.bbx
            Four::Double(4, 7),
            Four::Double(3, 6),
            // xbbb.b.bbbx
            Four::Double(4, 6),
            // ,,,x.bbbb.x
            // ,,x.bbbb.x,
            // ,x.bbbb.x,,
            // x.bbbb.x,,,
            Four::Straight(1, 6),
            Four::Straight(2, 7),
            Four::Straight(3, 8),
            Four::Straight(4, 9),
            // ,,,,xbbbb.x
            // ,,,xbbbb.x,
            // ,,xbbbb.x,,
            // ,xbbbb.x,,,
            Four::Normal(1),
            Four::Normal(2),
            Four::Normal(3),
            Four::Normal(4),
            // ,,,,xb.bbbx
            // ,,xb.bbbx,,
            // ,xb.bbbx,,,
            // xb.bbbx,,,,
            Four::Normal(4),
            Four::Normal(6),
            Four::Normal(7),
            Four::Normal(8),
            // ,,,,xbb.bbx
            // ,,,xbb.bbx,
            // ,xbb.bbx,,,
            // xbb.bbx,,,,
            Four::Normal(3),
            Four::Normal(4),
            Four::Normal(6),
            Four::Normal(7),
            // ,,,,xbbb.bx
            // ,,,xbbb.bx,
            // ,,xbbb.bx,,
            // xbbb.bx,,,,
            Four::Normal(2),
            Four::Normal(3),
            Four::Normal(4),
            Four::Normal(6),
            // ,,,x.bbbbx,
            // ,,x.bbbbx,,
            // ,x.bbbbx,,,
            // x.bbbbx,,,,
            Four::Normal(6),
            Four::Normal(7),
            Four::Normal(8),
            Four::Normal(9),
        ];

        debug_assert_eq!(FOUR_PATTERNS.len(), EMPTY_PATTERNS.len());
        debug_assert_eq!(EMPTY_PATTERNS.len(), NO_OURS_PATTERNS.len());
        debug_assert_eq!(NO_OURS_PATTERNS.len(), FIVE_OFFSETS.len());

        //TODO: check if better optimized with lazy iterators
        let mut i = 0;
        while i < FOUR_PATTERNS.len() {
            if (our_row & FOUR_PATTERNS[i]) == FOUR_PATTERNS[i]
                && (their_row & EMPTY_PATTERNS[i]) == 0
                && (our_row & EMPTY_PATTERNS[i]) == 0
                && (border_row & EMPTY_PATTERNS[i]) == 0
                && (our_row & NO_OURS_PATTERNS[i]) == 0
            {
                return Some(FIVE_OFFSETS[i].add(offset));
            }
            i += 1;
        }

        None
    }

    pub fn get_four(&self, pos: Pos, side: Side) -> Option<Four<Pos>> {
        let our_row = self.row_of(pos.row(), side);
        let their_row = self.row_of(pos.row(), side.opposite());
        let border_row = if SIZE == RENJU_BOARD_SIZE {
            Self::NORMAL_BOUNDARY_BOARD.row(pos.row())
        } else {
            Self::DIAGONAL_BOUNDARY_BOARD.row(pos.row())
        };

        match Self::get_four_impl(pos.col(), our_row, their_row, border_row) {
            Some(Four::Normal(col)) => Some(Four::Normal(Pos::new(pos.row(), col))),
            Some(Four::Straight(col1, col2)) => Some(Four::Straight(
                Pos::new(pos.row(), col1),
                Pos::new(pos.row(), col2),
            )),
            Some(Four::Double(col1, col2)) => Some(Four::Double(
                Pos::new(pos.row(), col1),
                Pos::new(pos.row(), col2),
            )),
            _ => None,
        }
    }

    // Possible patterns
    //
    // xbbbbbx
    //      v
    // xbbbbbx,,,,
    // ,xbbbbbx,,,
    // ,,xbbbbbx,,
    // ,,,xbbbbbx,
    // ,,,,xbbbbbx
    fn is_win_no_overline_impl(string: u64, idx: u8) -> bool {
        const MASK: u64 = (1 << 11) - 1;
        debug_assert!(idx >= 11);

        let offset = idx - 5;
        let string = ((string >> offset) & MASK) as u16;

        const WIN_PATTERNS: &[u16] = &[
            0b01111100000,
            0b00111110000,
            0b00011111000,
            0b00001111100,
            0b00000111110,
        ];

        const NO_OURS_PATTERNS: &[u16] = &[
            0b10000010000,
            0b01000001000,
            0b00100000100,
            0b00010000010,
            0b00001000001,
        ];

        WIN_PATTERNS
            .iter()
            .zip(NO_OURS_PATTERNS.iter())
            .any(|(win, empty)| ((string & win) == *win) && ((string & empty) == 0))
    }

    // Possible patterns
    //
    // bbbbbb
    //      v
    // bbbbbb,,,,,
    // ,bbbbbb,,,,
    // ,,bbbbbb,,,
    // ,,,bbbbbb,,
    // ,,,,bbbbbb,
    // ,,,,,bbbbbb
    fn is_overline_impl(string: u64, idx: u8) -> bool {
        const MASK: u64 = (1 << 11) - 1;
        debug_assert!(idx >= 5);

        let offset = idx - 5;
        let string = ((string >> offset) & MASK) as u16;

        const OVERLINE_PATTERNS: &[u16] = &[
            0b11111100000,
            0b01111110000,
            0b00111111000,
            0b00011111100,
            0b00001111110,
            0b00000111111,
        ];

        for pattern in OVERLINE_PATTERNS {
            if (string & pattern) == *pattern {
                return true;
            }
        }
        false
    }

    pub fn is_win_no_overline(&self, pos: Pos, side: Side) -> bool {
        let string = self.row_of(pos.row(), side);
        Self::is_win_no_overline_impl(string, pos.col())
    }

    pub fn is_overline(&self, pos: Pos, side: Side) -> bool {
        let string = self.row_of(pos.row(), side);
        Self::is_overline_impl(string, pos.col())
    }

    //NOTE you should probably not use this
    const fn is_oob(&self, pos: Pos) -> bool {
        pos.col() as usize >= SIZE || pos.row() as usize >= SIZE
    }
}

impl<const SIZE: usize> FromStr for PieceBoard<SIZE> {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.is_ascii() {
            bail!("must be ascii string");
        }

        let mut board = Self::new();

        let mut iter = s.chars().peekable();
        while let Some(ch) = iter.next() {
            if !ch.is_ascii_alphabetic() {
                bail!("not ascii alpha");
            }

            if ch.is_whitespace() {
                continue;
            }

            let side = if ch.is_ascii_lowercase() {
                Side::Black
            } else {
                Side::White
            };

            let col = ch.to_ascii_lowercase() as u8 - b'a';

            let mut row = String::new();

            while let Some(digit) = iter.peek().filter(|x| char::is_ascii_digit(x)) {
                row.push(*digit);
                iter.nth(0);
            }

            let row: u8 = row.parse()?;

            if row == 0 {
                bail!("row must be > 0");
            }

            let pos = Pos::new(row - 1, col);
            if board.is_oob(pos) {
                bail!("out of bounds");
            }

            board = board.set(pos, Some(side));
        }
        Ok(board)
    }
}

pub const RENJU_BOARD_SIZE: usize = 15;
pub const RENJU_BOARD_SIZEU8: u8 = RENJU_BOARD_SIZE as u8;
pub const RENJU_DIAG_BOARD_SIZE: usize = (RENJU_BOARD_SIZE * 2) - 1;
pub const RENJU_DIAG_BOARD_SIZEU8: u8 = RENJU_DIAG_BOARD_SIZE as u8;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Board {
    board0: PieceBoard<RENJU_BOARD_SIZE>,      // row major
    board1: PieceBoard<RENJU_BOARD_SIZE>,      // column major
    board2: PieceBoard<RENJU_DIAG_BOARD_SIZE>, // left bottom to right top
    board3: PieceBoard<RENJU_DIAG_BOARD_SIZE>, // left bottom to right top
}

impl Board {
    const MARGIN: u8 = (64 - RENJU_BOARD_SIZEU8) / 2;

    pub const fn new() -> Self {
        Self {
            board0: PieceBoard::new(),
            board1: PieceBoard::new(),
            board2: PieceBoard::new(),
            board3: PieceBoard::new(),
        }
    }

    pub const fn centre(pos: Pos) -> Pos {
        Pos::new(pos.row(), pos.col() + Self::MARGIN)
    }

    pub const fn decentre(pos: Pos) -> Pos {
        Pos::new(pos.row(), pos.col() - Self::MARGIN)
    }

    pub const fn transform_rowmajor(pos: Pos) -> Pos {
        Self::centre(pos)
    }

    pub const fn untransform_rowmajor(pos: Pos) -> Pos {
        Self::decentre(pos)
    }

    pub const fn transform_colmajor(pos: Pos) -> Pos {
        Self::centre(pos.transpose())
    }

    pub const fn untransform_colmajor(pos: Pos) -> Pos {
        Self::decentre(pos).transpose()
    }

    pub const fn set(mut self, pos: Pos, val: Option<Side>) -> Self {
        self.board0 = self.board0.set(Self::transform_rowmajor(pos), val);
        self.board1 = self.board1.set(Self::transform_colmajor(pos), val);
        self.board2 = self.board2.set(transform_right(pos), val);
        self.board3 = self.board3.set(transform_left(pos), val);
        self
    }

    pub const fn at(&self, pos: Pos) -> Option<Side> {
        let pos = Self::transform_rowmajor(pos);

        self.board0.at(pos)
    }

    pub fn check_self(&self) {
        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = (row, col).into();

                let val = self.board0.at(Self::transform_rowmajor(pos));

                debug_assert_eq!(self.board1.at(Self::transform_colmajor(pos)), val);
                debug_assert_eq!(self.board2.at(transform_right(pos)), val);
                debug_assert_eq!(self.board3.at(transform_left(pos)), val);
            }
        }
    }

    pub fn get_threes(&self, pos: Pos, side: Side) -> [Option<Three<Pos>>; 4] {
        [
            self.board0
                .get_three(Self::transform_rowmajor(pos), side)
                .map(|x| x.map(Self::untransform_rowmajor)),
            self.board1
                .get_three(Self::transform_colmajor(pos), side)
                .map(|x| x.map(Self::untransform_colmajor)),
            self.board2
                .get_three(transform_right(pos), side)
                .map(|x| x.map(untransform_right)),
            self.board3
                .get_three(transform_left(pos), side)
                .map(|x| x.map(untransform_left)),
        ]
    }

    pub fn get_fours(&self, pos: Pos, side: Side) -> [Option<Four<Pos>>; 4] {
        [
            self.board0
                .get_four(Self::transform_rowmajor(pos), side)
                .map(|x| x.map(Self::untransform_rowmajor)),
            self.board1
                .get_four(Self::transform_colmajor(pos), side)
                .map(|x| x.map(Self::untransform_colmajor)),
            self.board2
                .get_four(transform_right(pos), side)
                .map(|x| x.map(untransform_right)),
            self.board3
                .get_four(transform_left(pos), side)
                .map(|x| x.map(untransform_left)),
        ]
    }

    pub fn is_win_no_overline(&self, pos: Pos, side: Side) -> bool {
        self.board0
            .is_win_no_overline(Self::transform_rowmajor(pos), side)
            | self
                .board1
                .is_win_no_overline(Self::transform_colmajor(pos), side)
            | self.board2.is_win_no_overline(transform_right(pos), side)
            | self.board3.is_win_no_overline(transform_left(pos), side)
    }

    pub fn is_overline(&self, pos: Pos, side: Side) -> bool {
        self.board0.is_overline(Self::transform_rowmajor(pos), side)
            | self.board1.is_overline(Self::transform_colmajor(pos), side)
            | self.board2.is_overline(transform_right(pos), side)
            | self.board3.is_overline(transform_left(pos), side)
    }

    pub const fn size(&self) -> u8 {
        RENJU_BOARD_SIZE as u8
    }

    pub const fn normal_boundary_board() -> BitBoard<RENJU_BOARD_SIZE> {
        let mut board: BitBoard<RENJU_BOARD_SIZE> = BitBoard::filled();

        let mut row = 0;
        while row < RENJU_BOARD_SIZEU8 {
            let mut col = 0;
            while col < RENJU_BOARD_SIZEU8 {
                let pos = Pos::new(row, col);
                board = board.set(Self::transform_rowmajor(pos), false);
                col += 1;
            }
            row += 1;
        }
        board
    }

    //https://math.stackexchange.com/a/733222
    const fn rot_left(pos: Pos) -> Pos {
        Pos::new(
            pos.row() + pos.col(),
            (RENJU_BOARD_SIZEU8 - 1) - pos.row() + pos.col(),
        )
    }

    pub const fn rot_right(pos: Pos) -> Pos {
        Self::rot_left(pos).transpose()
    }

    const DIAG_CENTRE_COL: u8 = RENJU_DIAG_BOARD_SIZEU8 / 2;

    const fn squeeze(mut pos: Pos) -> Pos {
        pos = Pos::new(pos.row(), pos.col() - pos.col() / 2);
        pos
    }

    pub const fn transform_right(pos: Pos) -> Pos {
        Self::centre(Self::squeeze(Self::rot_right(pos)))
    }

    pub const fn transform_left(pos: Pos) -> Pos {
        Self::centre(Self::squeeze(Self::rot_left(pos)))
    }

    pub const fn diag_boundary_board() -> BitBoard<RENJU_DIAG_BOARD_SIZE> {
        let mut board: BitBoard<RENJU_DIAG_BOARD_SIZE> = BitBoard::filled();

        let mut row = 0;
        while row < RENJU_BOARD_SIZEU8 {
            let mut col = 0;
            while col < RENJU_BOARD_SIZEU8 {
                board = board.set(Self::transform_right(Pos::new(row, col)), false);
                col += 1;
            }
            row += 1;
        }

        board
    }

    fn is_double_four(&self, pos: Pos, side: Side) -> bool {
        self.get_fours(pos, side)
            .into_iter()
            .filter_map(std::convert::identity)
            .map(|four| match four {
                Four::Normal(_) | Four::Straight(_, _) => 1,
                Four::Double(_, _) => 2,
            })
            .sum::<u8>()
            >= 2
    }

    fn is_renju_forbidden(mut self, pos: Pos) -> bool {
        debug_assert_ne!(self.at(pos), Some(Side::White));

        let mut res = false;

        self = self.set(pos, Some(Side::Black));

        if !self.is_win_no_overline(pos, Side::Black) {
            if self.is_overline(pos, Side::Black) || self.is_double_four(pos, Side::Black) {
                res = true;
            } else {
                let mut actual = 0;

                for three in self
                    .get_threes(pos, Side::Black)
                    .into_iter()
                    .filter_map(std::convert::identity)
                {
                    let mut count = 0;
                    let mut blocked = 0;

                    for pos in three {
                        count += 1;

                        self = self.set(pos, Some(Side::Black));

                        if self.is_win_no_overline(pos, Side::Black) || self.is_renju_forbidden(pos)
                        {
                            blocked += 1;
                        }

                        self = self.set(pos, None);
                    }

                    if blocked < count {
                        actual += 1;
                    }
                }
                res = actual >= 2;
            }
        }

        //self = self.set(pos, None);

        res
    }

    pub fn construct_bitboard<F>(mut self, f: F) -> BitBoard<RENJU_BOARD_SIZE>
    where
        F: Fn(&Self, Pos, Side) -> bool,
    {
        let mut res = BitBoard::new();

        for pos in self.positions() {
            if self.at(pos) != None {
                continue;
            }

            self = self.set(pos, Some(Side::Black));
            res = res.set(pos, f(&self, pos, Side::Black));
            self = self.set(pos, None);
        }
        res
    }

    pub fn win(self) -> BitBoard<RENJU_BOARD_SIZE> {
        self.construct_bitboard(Self::is_win_no_overline)
    }

    pub fn overline(self) -> BitBoard<RENJU_BOARD_SIZE> {
        self.construct_bitboard(Self::is_overline)
    }

    pub fn double_fours(self) -> BitBoard<RENJU_BOARD_SIZE> {
        self.construct_bitboard(Self::is_double_four)
    }

    pub fn threes(self) -> BitBoard<RENJU_BOARD_SIZE> {
        self.construct_bitboard(|board, pos, side| {
            board
                .get_threes(pos, side)
                .into_iter()
                .any(|three| three.is_some())
        })
    }

    pub fn renju_forbidden(self) -> BitBoard<RENJU_BOARD_SIZE> {
        let mut forbidden = BitBoard::new();

        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = (row, col).into();
                if self.at(pos) != None {
                    //Already taken
                    continue;
                }

                //TODO make sure that it doesn't create a copy of the board for the check, is not
                //needed as the board is returned to original state
                forbidden = forbidden.set(pos, self.is_renju_forbidden(pos));
            }
        }
        forbidden
    }

    pub fn transform<F>(&self, f: F) -> Self
    where
        F: Fn(Pos) -> Pos,
    {
        let mut board = Board::new();

        for pos in board.positions() {
            if let Some(side) = self.at(pos) {
                board = board.set(f(pos), Some(side));
            }
        }
        board
    }

    #[cfg(test)]
    pub fn gen_table<F: Fn(Pos) -> Pos>(name: &str, f: F) {
        let mut transformed = HashMap::new();
        let mut inverse = HashMap::new();

        let mut max_row = 0;
        let mut max_col = 0;

        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = Pos::new(row, col);

                let tpos = f(pos);

                max_row = max_row.max(tpos.row());
                max_col = max_col.max(tpos.col());

                transformed.insert(pos, tpos);
                inverse.insert(tpos, pos);
            }
        }
        print!("const {}_TABLE: &'static [&'static [Pos]] = &[", name);

        for row in 0..RENJU_BOARD_SIZEU8 {
            print!("&[");
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = Pos::new(row, col);
                if let Some(tpos) = transformed.get(&pos) {
                    print!("Pos::new({}, {}),", tpos.row(), tpos.col());
                } else {
                    panic!("this should not happen");
                }
            }
            println!("],");
        }
        println!("];");

        println!(
            "const INVERSE_{}_TABLE: &'static [&'static [Pos]] = &[",
            name
        );
        for row in 0..=max_row {
            print!("&[");
            for col in 0..=max_col {
                let pos = Pos::new(row, col);
                print!("Pos::new(");
                if let Some(tpos) = inverse.get(&pos) {
                    print!("{}, {}", tpos.row(), tpos.col());
                } else {
                    print!("1000,1000");
                }
                print!("),");
            }
            println!("],");
        }
        println!("];");
    }

    pub fn flip(&self) -> Self {
        self.transform(|pos| Pos::new(self.size() - pos.row() - 1, self.size() - pos.col() - 1))
    }

    pub fn positions(&self) -> impl Iterator<Item = Pos> {
        let size = self.size();
        std::iter::successors(Some(Pos::new(0, 0)), move |prev| {
            let next_row = prev.row() + 1;
            let next_col = prev.col() + 1;

            if next_col < size {
                Some((prev.row(), next_col).into())
            } else if next_row < size {
                Some((next_row, 0).into())
            } else {
                None
            }
        })
    }

    pub fn squares(&self) -> impl Iterator<Item = (Pos, Option<Side>)> + '_ {
        self.positions().map(|pos| (pos, self.at(pos)))
    }

    pub fn pieces(&self) -> impl Iterator<Item = (Pos, Side)> + '_ {
        self.squares().filter_map(|(pos, square)| match square {
            Some(side) => Some((pos, side)),
            _ => None,
        })
    }
}

impl FromStr for Board {
    type Err = <PieceBoard<RENJU_BOARD_SIZE> as FromStr>::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let board: PieceBoard<RENJU_BOARD_SIZE> = s.parse()?;
        let mut res = Self::new();

        for row in 0..RENJU_BOARD_SIZE {
            for col in 0..RENJU_BOARD_SIZE {
                let pos = Pos::new(row as u8, col as u8);
                res = res.set(pos, board.at(pos));
            }
        }
        Ok(res)
    }
}

impl fmt::Display for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = Pos::new(row, col);

                if let Some(side) = self.at(pos) {
                    let s = if side == Side::White {
                        pos.to_string().to_uppercase()
                    } else {
                        pos.to_string()
                    };

                    write!(f, "{}", s)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::board::{
        BitBoard, Board, PieceBoard, Side, Three, RENJU_BOARD_SIZE, RENJU_BOARD_SIZEU8,
    };
    use crate::table::*;
    use anyhow::Result;
    use std::collections::HashSet;
    use tools::Pos;

    #[test]
    fn place_and_remove_bitboard() {
        let mut board: BitBoard<15> = BitBoard::new();

        let pos = Pos::new(4, 6);
        board = board.set(pos, true);
        assert_eq!(board.at(pos), true);

        board = board.set(pos, false);
        assert_eq!(board.at(pos), false);
    }

    #[test]
    fn parse_empty_board() {
        const SIZE: usize = 15;
        let board: PieceBoard<SIZE> = "".parse().unwrap();

        //board.check_self();
        for row in 0..SIZE {
            for col in 0..SIZE {
                assert_eq!(board.at((row as u8, col as u8).into()), None);
            }
        }
    }

    #[test]
    fn parse_pos() {
        assert_eq!("a1".parse::<Pos>().unwrap(), Pos::new(0, 0));
        assert_eq!("h8".parse::<Pos>().unwrap(), Pos::new(7, 7));
        assert_eq!("a2".parse::<Pos>().unwrap(), Pos::new(1, 0));
        assert_eq!("o15".parse::<Pos>().unwrap(), Pos::new(14, 14));
        assert_eq!("z6".parse::<Pos>().unwrap(), Pos::new(5, 25));
    }

    #[test]
    fn pos_round_trip() {
        for row in 0..26 {
            for col in 0..26 {
                let pos = Pos::new(row, col);
                let string = pos.to_string();
                assert_eq!(string.parse::<Pos>().unwrap(), pos);
            }
        }
    }

    fn test_board_one_piece(b: &str) {
        assert!(b.is_ascii());
        let side = if (b.as_bytes()[0] as char).is_ascii_lowercase() {
            Side::Black
        } else {
            Side::White
        };

        let board: Board = b.parse().unwrap();
        board.check_self();
        assert_eq!(board.at(b.parse().unwrap()), Some(side));
    }

    #[test]
    fn parse_single_piece() {
        test_board_one_piece("a1");
        test_board_one_piece("A1");
        test_board_one_piece("m6");
        test_board_one_piece("e12");
        test_board_one_piece("E12");
        test_board_one_piece("g2");
    }

    #[test]
    fn parse_board() -> Result<()> {
        let board: PieceBoard<15> = "g7N4c7E12i4E2i9G9e6g6".parse()?;

        assert_eq!(board.at("g7".parse()?), Some(Side::Black));
        assert_eq!(board.at("n4".parse()?), Some(Side::White));
        assert_eq!(board.at("c7".parse()?), Some(Side::Black));
        assert_eq!(board.at("e12".parse()?), Some(Side::White));
        assert_eq!(board.at("i4".parse()?), Some(Side::Black));
        assert_eq!(board.at("e2".parse()?), Some(Side::White));
        assert_eq!(board.at("i9".parse()?), Some(Side::Black));
        assert_eq!(board.at("g9".parse()?), Some(Side::White));
        assert_eq!(board.at("e6".parse()?), Some(Side::Black));
        assert_eq!(board.at("e6".parse()?), Some(Side::Black));
        Ok(())
    }

    #[test]
    fn detect_three1() -> Result<()> {
        let three = PieceBoard::<15>::get_three_impl(14, 0b111 << 15, 0, 0);
        assert_eq!(three, None);
        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 15, 0, 0);
        assert_eq!(three, Some(Three::Straight(14, 18)));
        let three = PieceBoard::<15>::get_three_impl(16, 0b111 << 15, 0, 0);
        assert_eq!(three, Some(Three::Straight(14, 18)));
        let three = PieceBoard::<15>::get_three_impl(17, 0b111 << 15, 0, 0);
        assert_eq!(three, Some(Three::Straight(14, 18)));
        let three = PieceBoard::<15>::get_three_impl(18, 0b111 << 15, 0, 0);
        assert_eq!(three, None);

        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 16, 0, 0);
        assert_eq!(three, None);
        let three = PieceBoard::<15>::get_three_impl(16, 0b111 << 16, 0, 0);
        assert_eq!(three, Some(Three::Straight(15, 19)));

        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 15, 0b0001 << 14, 0);
        assert_eq!(three, None);
        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 15, 0b10000 << 14, 0);
        assert_eq!(three, None);
        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 15, 0, 0b0001 << 14);
        assert_eq!(three, None);
        let three = PieceBoard::<15>::get_three_impl(15, 0b111 << 15, 0, 0b10000 << 14);
        assert_eq!(three, None);
        Ok(())
    }

    #[test]
    fn three_equality() {
        let a: Three<u8> = Three::Normal(1);
        let b: Three<u8> = Three::Normal(2);
        let c: Three<u8> = Three::Normal(1);
        let d: Three<u8> = Three::Straight(42, 21);
        let e: Three<u8> = Three::Straight(21, 42);
        let f: Three<u8> = Three::Straight(51, 34);

        assert_eq!(a, c);
        assert_eq!(c, a);
        assert_ne!(a, b);
        assert_ne!(b, a);
        assert_ne!(a, d);
        assert_ne!(a, e);
        assert_ne!(a, f);

        assert_ne!(d, a);
        assert_ne!(e, a);
        assert_ne!(f, a);
        assert_ne!(d, b);
        assert_ne!(e, b);
        assert_ne!(f, b);

        assert_eq!(d, e);
        assert_eq!(e, d);

        assert_ne!(d, f);
        assert_ne!(f, d);

        assert_ne!(e, f);
        assert_ne!(f, e);
    }

    #[test]
    fn parse_empty_renju_board() {
        let board: Board = "".parse().unwrap();

        board.check_self();
        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                assert_eq!(board.at((row as u8, col as u8).into()), None);
            }
        }
    }

    fn test_renju_board_one_piece(b: &str) {
        assert!(b.is_ascii());
        let side = if (b.as_bytes()[0] as char).is_ascii_lowercase() {
            Side::Black
        } else {
            Side::White
        };

        let board: Board = b.parse().unwrap();
        assert_eq!(board.at(b.parse().unwrap()), Some(side));
    }

    #[test]
    fn parse_single_piece_renju() {
        test_renju_board_one_piece("a1");
        test_renju_board_one_piece("A1");
        test_renju_board_one_piece("m6");
        test_renju_board_one_piece("e12");
        test_renju_board_one_piece("E12");
        test_renju_board_one_piece("g2");
    }

    fn test_three(board: &str, pos: &str, threes: &[&str]) {
        let pos = pos.parse().unwrap();
        let board: Board = board.parse().unwrap();
        let threes: HashSet<Pos> = threes.iter().map(|x| x.parse().unwrap()).collect();

        let res = board
            .get_threes(pos, Side::Black)
            .iter()
            .cloned()
            .filter_map(std::convert::identity)
            .flatten()
            .collect();
        assert_eq!(threes, res);
    }

    #[test]
    fn horizontal_three() {
        test_three("g8h8i8", "d8", &[]);
        test_three("g8h8i8", "e8", &[]);
        test_three("g8h8i8", "f8", &[]);
        test_three("g8h8i8", "g8", &["f8", "j8"]);
        test_three("g8h8i8", "h8", &["f8", "j8"]);
        test_three("g8h8i8", "i8", &["f8", "j8"]);
        test_three("g8h8i8", "j8", &[]);
        test_three("g8h8i8", "k8", &[]);
        test_three("g8h8i8", "l8", &[]);

        test_three("f8g8h8i8", "c8", &[]);
        test_three("f8g8h8i8", "d8", &[]);
        test_three("f8g8h8i8", "e8", &[]);
        test_three("f8g8h8i8", "f8", &[]);
        test_three("f8g8h8i8", "g8", &[]);
        test_three("f8g8h8i8", "h8", &[]);
        test_three("f8g8h8i8", "i8", &[]);
        test_three("f8g8h8i8", "j8", &[]);
        test_three("f8g8h8i8", "k8", &[]);
        test_three("f8g8h8i8", "l8", &[]);
        test_three("f8g8h8i8", "m8", &[]);

        test_three("f8g8h8i8k8", "c8", &[]);
        test_three("f8g8h8i8k8", "d8", &[]);
        test_three("f8g8h8i8k8", "e8", &[]);
        test_three("f8g8h8i8k8", "f8", &[]);
        test_three("f8g8h8i8k8", "g8", &[]);
        test_three("f8g8h8i8k8", "h8", &[]);
        test_three("f8g8h8i8k8", "i8", &[]);
        test_three("f8g8h8i8k8", "j8", &[]);
        test_three("f8g8h8i8k8", "k8", &[]);
        test_three("f8g8h8i8k8", "l8", &[]);
        test_three("f8g8h8i8k8", "m8", &[]);

        test_three("e8g8h8i8", "b8", &[]);
        test_three("e8g8h8i8", "c8", &[]);
        test_three("e8g8h8i8", "d8", &[]);
        test_three("e8g8h8i8", "f8", &[]);
        test_three("e8g8h8i8", "g8", &[]);
        test_three("e8g8h8i8", "h8", &[]);
        test_three("e8g8h8i8", "i8", &[]);
        test_three("e8g8h8i8", "j8", &[]);
        test_three("e8g8h8i8", "k8", &[]);
        test_three("e8g8h8i8", "l8", &[]);
        test_three("e8g8h8i8", "m8", &[]);

        test_three("g8h8i8k8", "b8", &[]);
        test_three("g8h8i8k8", "c8", &[]);
        test_three("g8h8i8k8", "d8", &[]);
        test_three("g8h8i8k8", "f8", &[]);
        test_three("g8h8i8k8", "g8", &[]);
        test_three("g8h8i8k8", "h8", &[]);
        test_three("g8h8i8k8", "i8", &[]);
        test_three("g8h8i8k8", "j8", &[]);
        test_three("g8h8i8k8", "k8", &[]);
        test_three("g8h8i8k8", "l8", &[]);
        test_three("g8h8i8k8", "m8", &[]);
        test_three("g8h8i8k8", "n8", &[]);

        test_three("E8g8h8i8", "d8", &[]);
        test_three("E8g8h8i8", "e8", &[]);
        test_three("E8g8h8i8", "f8", &[]);
        test_three("E8g8h8i8", "g8", &["j8"]);
        test_three("E8g8h8i8", "h8", &["j8"]);
        test_three("E8g8h8i8", "i8", &["j8"]);
        test_three("E8g8h8i8", "j8", &[]);
        test_three("E8g8h8i8", "k8", &[]);
        test_three("E8g8h8i8", "l8", &[]);

        test_three("g8h8i8K8", "d8", &[]);
        test_three("g8h8i8K8", "e8", &[]);
        test_three("g8h8i8K8", "f8", &[]);
        test_three("g8h8i8K8", "g8", &["f8"]);
        test_three("g8h8i8K8", "h8", &["f8"]);
        test_three("g8h8i8K8", "i8", &["f8"]);
        test_three("g8h8i8K8", "j8", &[]);
        test_three("g8h8i8K8", "k8", &[]);
        test_three("g8h8i8K8", "l8", &[]);

        test_three("g8h8i8l8", "d8", &[]);
        test_three("g8h8i8l8", "e8", &[]);
        test_three("g8h8i8l8", "f8", &[]);
        test_three("g8h8i8l8", "g8", &["f8"]);
        test_three("g8h8i8l8", "h8", &["f8"]);
        test_three("g8h8i8l8", "i8", &["f8"]);
        test_three("g8h8i8l8", "j8", &[]);
        test_three("g8h8i8l8", "k8", &[]);
        test_three("g8h8i8l8", "l8", &[]);

        test_three("d8g8h8i8", "d8", &[]);
        test_three("d8g8h8i8", "e8", &[]);
        test_three("d8g8h8i8", "f8", &[]);
        test_three("d8g8h8i8", "g8", &["j8"]);
        test_three("d8g8h8i8", "h8", &["j8"]);
        test_three("d8g8h8i8", "i8", &["j8"]);
        test_three("d8g8h8i8", "j8", &[]);
        test_three("d8g8h8i8", "k8", &[]);
        test_three("d8g8h8i8", "l8", &[]);

        test_three("D8g8h8i8", "d8", &[]);
        test_three("D8g8h8i8", "e8", &[]);
        test_three("D8g8h8i8", "f8", &[]);
        test_three("D8g8h8i8", "g8", &["f8", "j8"]);
        test_three("D8g8h8i8", "h8", &["f8", "j8"]);
        test_three("D8g8h8i8", "i8", &["f8", "j8"]);
        test_three("D8g8h8i8", "j8", &[]);
        test_three("D8g8h8i8", "k8", &[]);
        test_three("D8g8h8i8", "l8", &[]);

        test_three("g8h8i8L8", "d8", &[]);
        test_three("g8h8i8L8", "e8", &[]);
        test_three("g8h8i8L8", "f8", &[]);
        test_three("g8h8i8L8", "g8", &["f8", "j8"]);
        test_three("g8h8i8L8", "h8", &["f8", "j8"]);
        test_three("g8h8i8L8", "i8", &["f8", "j8"]);
        test_three("g8h8i8L8", "j8", &[]);
        test_three("g8h8i8L8", "k8", &[]);
        test_three("g8h8i8L8", "l8", &[]);

        test_three("D8g8h8i8L8", "d8", &[]);
        test_three("D8g8h8i8L8", "e8", &[]);
        test_three("D8g8h8i8L8", "f8", &[]);
        test_three("D8g8h8i8L8", "g8", &["f8", "j8"]);
        test_three("D8g8h8i8L8", "h8", &["f8", "j8"]);
        test_three("D8g8h8i8L8", "i8", &["f8", "j8"]);
        test_three("D8g8h8i8L8", "j8", &[]);
        test_three("D8g8h8i8L8", "k8", &[]);
        test_three("D8g8h8i8L8", "l8", &[]);

        test_three("l8m8n8", "i8", &[]);
        test_three("l8m8n8", "j8", &[]);
        test_three("l8m8n8", "k8", &[]);
        test_three("l8m8n8", "l8", &["k8"]);
        test_three("l8m8n8", "m8", &["k8"]);
        test_three("l8m8n8", "n8", &["k8"]);
        test_three("l8m8n8", "o8", &[]);

        test_three("k8l8m8", "h8", &[]);
        test_three("k8l8m8", "i8", &[]);
        test_three("k8l8m8", "j8", &[]);
        test_three("k8l8m8", "k8", &["j8", "n8"]);
        test_three("k8l8m8", "l8", &["j8", "n8"]);
        test_three("k8l8m8", "m8", &["j8", "n8"]);
        test_three("k8l8m8", "n8", &[]);
        test_three("k8l8m8", "o8", &[]);

        test_three("b8c8d8", "a8", &[]);
        test_three("b8c8d8", "b8", &["e8"]);
        test_three("b8c8d8", "c8", &["e8"]);
        test_three("b8c8d8", "d8", &["e8"]);
        test_three("b8c8d8", "e8", &[]);
        test_three("b8c8d8", "f8", &[]);
        test_three("b8c8d8", "g8", &[]);

        test_three("c8d8e8", "a8", &[]);
        test_three("c8d8e8", "b8", &[]);
        test_three("c8d8e8", "c8", &["b8", "f8"]);
        test_three("c8d8e8", "d8", &["b8", "f8"]);
        test_three("c8d8e8", "e8", &["b8", "f8"]);
        test_three("c8d8e8", "f8", &[]);
        test_three("c8d8e8", "g8", &[]);
        test_three("c8d8e8", "h8", &[]);
    }

    #[test]
    fn vertical_three() {
        test_three("h7h8h9", "h12", &[]);
        test_three("h7h8h9", "h11", &[]);
        test_three("h7h8h9", "h10", &[]);
        test_three("h7h8h9", "h9", &["h10", "h6"]);
        test_three("h7h8h9", "h8", &["h10", "h6"]);
        test_three("h7h8h9", "h7", &["h10", "h6"]);
        test_three("h7h8h9", "h6", &[]);
        test_three("h7h8h9", "h5", &[]);
        test_three("h7h8h9", "h4", &[]);

        test_three("h7h8h9h10", "h13", &[]);
        test_three("h7h8h9h10", "h12", &[]);
        test_three("h7h8h9h10", "h11", &[]);
        test_three("h7h8h9h10", "h10", &[]);
        test_three("h7h8h9h10", "h9", &[]);
        test_three("h7h8h9h10", "h8", &[]);
        test_three("h7h8h9h10", "h7", &[]);
        test_three("h7h8h9h10", "h6", &[]);
        test_three("h7h8h9h10", "h5", &[]);
        test_three("h7h8h9h10", "h4", &[]);
        test_three("h7h8h9h10", "h3", &[]);

        test_three("h6h7h8h9", "h13", &[]);
        test_three("h6h7h8h9", "h12", &[]);
        test_three("h6h7h8h9", "h11", &[]);
        test_three("h6h7h8h9", "h10", &[]);
        test_three("h6h7h8h9", "h9", &[]);
        test_three("h6h7h8h9", "h8", &[]);
        test_three("h6h7h8h9", "h7", &[]);
        test_three("h6h7h8h9", "h6", &[]);
        test_three("h6h7h8h9", "h5", &[]);
        test_three("h6h7h8h9", "h4", &[]);
        test_three("h6h7h8h9", "h3", &[]);

        test_three("h5h7h8h9", "h13", &[]);
        test_three("h5h7h8h9", "h12", &[]);
        test_three("h5h7h8h9", "h11", &[]);
        test_three("h5h7h8h9", "h10", &[]);
        test_three("h5h7h8h9", "h9", &[]);
        test_three("h5h7h8h9", "h8", &[]);
        test_three("h5h7h8h9", "h7", &[]);
        test_three("h5h7h8h9", "h6", &[]);
        test_three("h5h7h8h9", "h5", &[]);
        test_three("h5h7h8h9", "h4", &[]);
        test_three("h5h7h8h9", "h3", &[]);
        test_three("h5h7h8h9", "h2", &[]);

        test_three("h7h8h9h11", "h14", &[]);
        test_three("h7h8h9h11", "h13", &[]);
        test_three("h7h8h9h11", "h12", &[]);
        test_three("h7h8h9h11", "h11", &[]);
        test_three("h7h8h9h11", "h10", &[]);
        test_three("h7h8h9h11", "h9", &[]);
        test_three("h7h8h9h11", "h8", &[]);
        test_three("h7h8h9h11", "h7", &[]);
        test_three("h7h8h9h11", "h6", &[]);
        test_three("h7h8h9h11", "h5", &[]);
        test_three("h7h8h9h11", "h4", &[]);
        test_three("h7h8h9h11", "h3", &[]);

        test_three("H5h7h8h9", "h13", &[]);
        test_three("H5h7h8h9", "h12", &[]);
        test_three("H5h7h8h9", "h11", &[]);
        test_three("H5h7h8h9", "h10", &[]);
        test_three("H5h7h8h9", "h9", &["h10"]);
        test_three("H5h7h8h9", "h8", &["h10"]);
        test_three("H5h7h8h9", "h7", &["h10"]);
        test_three("H5h7h8h9", "h6", &[]);
        test_three("H5h7h8h9", "h5", &[]);
        test_three("H5h7h8h9", "h4", &[]);
        test_three("H5h7h8h9", "h3", &[]);
        test_three("H5h7h8h9", "h2", &[]);

        test_three("h7h8h9H11", "h14", &[]);
        test_three("h7h8h9H11", "h13", &[]);
        test_three("h7h8h9H11", "h12", &[]);
        test_three("h7h8h9H11", "h11", &[]);
        test_three("h7h8h9H11", "h10", &[]);
        test_three("h7h8h9H11", "h9", &["h6"]);
        test_three("h7h8h9H11", "h8", &["h6"]);
        test_three("h7h8h9H11", "h7", &["h6"]);
        test_three("h7h8h9H11", "h6", &[]);
        test_three("h7h8h9H11", "h5", &[]);
        test_three("h7h8h9H11", "h4", &[]);
        test_three("h7h8h9H11", "h3", &[]);

        test_three("h4h7h8h9", "h13", &[]);
        test_three("h4h7h8h9", "h12", &[]);
        test_three("h4h7h8h9", "h11", &[]);
        test_three("h4h7h8h9", "h10", &[]);
        test_three("h4h7h8h9", "h9", &["h10"]);
        test_three("h4h7h8h9", "h8", &["h10"]);
        test_three("h4h7h8h9", "h7", &["h10"]);
        test_three("h4h7h8h9", "h6", &[]);
        test_three("h4h7h8h9", "h5", &[]);
        test_three("h4h7h8h9", "h4", &[]);
        test_three("h4h7h8h9", "h3", &[]);
        test_three("h4h7h8h9", "h2", &[]);

        test_three("h7h8h9h12", "h14", &[]);
        test_three("h7h8h9h12", "h13", &[]);
        test_three("h7h8h9h12", "h12", &[]);
        test_three("h7h8h9h12", "h11", &[]);
        test_three("h7h8h9h12", "h10", &[]);
        test_three("h7h8h9h12", "h9", &["h6"]);
        test_three("h7h8h9h12", "h8", &["h6"]);
        test_three("h7h8h9h12", "h7", &["h6"]);
        test_three("h7h8h9h12", "h6", &[]);
        test_three("h7h8h9h12", "h5", &[]);
        test_three("h7h8h9h12", "h4", &[]);
        test_three("h7h8h9h12", "h3", &[]);

        test_three("H4h7h8h9", "h13", &[]);
        test_three("H4h7h8h9", "h12", &[]);
        test_three("H4h7h8h9", "h11", &[]);
        test_three("H4h7h8h9", "h10", &[]);
        test_three("H4h7h8h9", "h9", &["h6", "h10"]);
        test_three("H4h7h8h9", "h8", &["h6", "h10"]);
        test_three("H4h7h8h9", "h7", &["h6", "h10"]);
        test_three("H4h7h8h9", "h6", &[]);
        test_three("H4h7h8h9", "h5", &[]);
        test_three("H4h7h8h9", "h4", &[]);
        test_three("H4h7h8h9", "h3", &[]);
        test_three("H4h7h8h9", "h2", &[]);

        test_three("h7h8h9H12", "h14", &[]);
        test_three("h7h8h9H12", "h13", &[]);
        test_three("h7h8h9H12", "h12", &[]);
        test_three("h7h8h9H12", "h11", &[]);
        test_three("h7h8h9H12", "h10", &[]);
        test_three("h7h8h9H12", "h9", &["h6", "h10"]);
        test_three("h7h8h9H12", "h8", &["h6", "h10"]);
        test_three("h7h8h9H12", "h7", &["h6", "h10"]);
        test_three("h7h8h9H12", "h6", &[]);
        test_three("h7h8h9H12", "h5", &[]);
        test_three("h7h8h9H12", "h4", &[]);
        test_three("h7h8h9H12", "h3", &[]);

        test_three("H4h7h8h9H12", "h14", &[]);
        test_three("H4h7h8h9H12", "h13", &[]);
        test_three("H4h7h8h9H12", "h12", &[]);
        test_three("H4h7h8h9H12", "h11", &[]);
        test_three("H4h7h8h9H12", "h10", &[]);
        test_three("H4h7h8h9H12", "h9", &["h6", "h10"]);
        test_three("H4h7h8h9H12", "h8", &["h6", "h10"]);
        test_three("H4h7h8h9H12", "h7", &["h6", "h10"]);
        test_three("H4h7h8h9H12", "h6", &[]);
        test_three("H4h7h8h9H12", "h5", &[]);
        test_three("H4h7h8h9H12", "h4", &[]);
        test_three("H4h7h8h9H12", "h3", &[]);

        test_three("h12h13h14", "h15", &[]);
        test_three("h12h13h14", "h14", &["h11"]);
        test_three("h12h13h14", "h13", &["h11"]);
        test_three("h12h13h14", "h12", &["h11"]);
        test_three("h12h13h14", "h11", &[]);
        test_three("h12h13h14", "h10", &[]);
        test_three("h12h13h14", "h9", &[]);

        test_three("h11h12h13", "h15", &[]);
        test_three("h11h12h13", "h14", &[]);
        test_three("h11h12h13", "h13", &["h14", "h10"]);
        test_three("h11h12h13", "h12", &["h14", "h10"]);
        test_three("h11h12h13", "h11", &["h14", "h10"]);
        test_three("h11h12h13", "h10", &[]);
        test_three("h11h12h13", "h9", &[]);
        test_three("h11h12h13", "h8", &[]);

        test_three("h2h3h4", "h1", &[]);
        test_three("h2h3h4", "h2", &["h5"]);
        test_three("h2h3h4", "h3", &["h5"]);
        test_three("h2h3h4", "h4", &["h5"]);
        test_three("h2h3h4", "h5", &[]);
        test_three("h2h3h4", "h6", &[]);
        test_three("h2h3h4", "h7", &[]);

        test_three("h3h4h5", "h1", &[]);
        test_three("h3h4h5", "h2", &[]);
        test_three("h3h4h5", "h3", &["h2", "h6"]);
        test_three("h3h4h5", "h4", &["h2", "h6"]);
        test_three("h3h4h5", "h5", &["h2", "h6"]);
        test_three("h3h4h5", "h6", &[]);
        test_three("h3h4h5", "h7", &[]);
        test_three("h3h4h5", "h8", &[]);

        test_three_all_transposed("g8i8j8", &["g8", "i8", "j8"], &["h8"]);
        test_three_all_transposed("f8g8i8", &["f8", "g8", "i8"], &["h8"]);

        test_three_all_transposed("f8g8i8j8", &[], &[]);
        test_three_all_transposed("f8g8i8j8", &[], &[]);

        test_three_all_transposed("F8g8i8j8", &[], &[]);
        test_three_all_transposed("f8g8i8J8", &[], &[]);

        test_three_all_transposed("g8i8j8H8", &[], &[]);
        test_three_all_transposed("f8g8i8H8", &[], &[]);

        test_three_all_transposed("E8g8i8j8", &["g8", "i8", "j8"], &["h8"]);
        test_three_all_transposed("f8g8i8K8", &["f8", "g8", "i8"], &["h8"]);
        test_three_all_transposed("E8g8i8j8L8", &["g8", "i8", "j8"], &["h8"]);
        test_three_all_transposed("D8f8g8i8K8", &["f8", "g8", "i8"], &["h8"]);

        test_three_all_transposed("e8g8i8j8", &[], &[]);
        test_three_all_transposed("f8g8i8k8", &[], &[]);
        test_three_all_transposed("e8g8i8j8l8", &[], &[]);
        test_three_all_transposed("d8f8g8i8k8", &[], &[]);

        test_three_all_transposed("d8g8i8j8", &["g8", "i8", "j8"], &["h8"]);
        test_three_all_transposed("f8g8i8l8", &["f8", "g8", "i8"], &["h8"]);
        test_three_all_transposed("d8g8i8j8m8", &["g8", "i8", "j8"], &["h8"]);
        test_three_all_transposed("c8f8g8i8l8", &["f8", "g8", "i8"], &["h8"]);
    }

    #[test]
    fn test_double_threes() {
        test_three("h11f12h12k13k14k15i12", "i12", &["j13", "g12"]);
        test_three("h11j11f12h12e13k13f14k14c15k15i12", "i12", &["j13", "g12"]);
    }

    #[test]
    fn test_transforms() {
        for row in 0..RENJU_BOARD_SIZEU8 {
            for col in 0..RENJU_BOARD_SIZEU8 {
                let pos = Pos::new(row, col);

                assert_eq!(Board::transform_right(pos), transform_right(pos));
                assert_eq!(Board::transform_left(pos), transform_left(pos));

                assert_eq!(untransform_right(transform_right(pos)), pos);
                assert_eq!(untransform_left(transform_left(pos)), pos);
            }
        }
    }

    fn test_three_all_transformed<F>(board: &str, three_pieces: &[&str], four_pos: &[&str], f: F)
    where
        F: Fn(Pos) -> Pos,
    {
        let board = board.parse::<Board>().unwrap().transform(&f);

        let three_pieces: HashSet<Pos> = three_pieces
            .iter()
            .map(|x| x.parse::<Pos>().unwrap())
            .map(&f)
            .collect();
        let actual_fours: HashSet<Pos> = four_pos
            .iter()
            .map(|x| x.parse::<Pos>().unwrap())
            .map(&f)
            .collect();

        for pos in board.positions() {
            let fours = board
                .get_threes(pos, Side::Black)
                .into_iter()
                .filter_map(std::convert::identity)
                .flatten()
                .collect();
            if three_pieces.contains(&pos) {
                assert_eq!(actual_fours, fours);
            } else {
                assert!(fours.is_empty());
            }
        }
    }

    fn test_three_all_transposed(board: &str, three_pieces: &[&str], four_pos: &[&str]) {
        test_three_all_transformed(board, three_pieces, four_pos, std::convert::identity);
        test_three_all_transformed(board, three_pieces, four_pos, Pos::transpose);
    }

    fn test_three_all_transformed_flipped<F>(
        board: &str,
        three_pieces: &[&str],
        four_pos: &[&str],
        f: F,
    ) where
        F: Fn(Pos) -> Pos,
    {
        test_three_all_transformed(board, three_pieces, four_pos, &f);
        test_three_all_transformed(board, three_pieces, four_pos, |pos| {
            let pos = f(pos);
            Pos::new((RENJU_BOARD_SIZEU8 - 1) - pos.row(), pos.col())
        });
    }

    fn test_three_all_flipped(board: &str, three_pieces: &[&str], four_pos: &[&str]) {
        test_three_all_transformed(board, three_pieces, four_pos, std::convert::identity);
        test_three_all_transformed(board, three_pieces, four_pos, |pos| {
            Pos::new((RENJU_BOARD_SIZEU8 - 1) - pos.row(), pos.col())
        });
    }

    #[test]
    fn diag_three1() {
        test_three_all_flipped("", &[], &[]);
        test_three_all_flipped("h8", &[], &[]);
        test_three_all_flipped("h8i9", &[], &[]);
        test_three_all_flipped("g7h8", &[], &[]);

        test_three_all_flipped("g7h8i9", &["g7", "h8", "i9"], &["f6", "j10"]);
        test_three_all_flipped("f6g7h8i9", &[], &[]);
        test_three_all_flipped("g7h8i9j10", &[], &[]);
        test_three_all_flipped("e5g7h8i9", &[], &[]);
        test_three_all_flipped("g7h8i9k11", &[], &[]);
        test_three_all_flipped("E5g7h8i9", &["g7", "h8", "i9"], &["j10"]);
        test_three_all_flipped("g7h8i9K11", &["g7", "h8", "i9"], &["f6"]);
        test_three_all_flipped("D4g7h8i9", &["g7", "h8", "i9"], &["j10", "f6"]);
        test_three_all_flipped("g7h8i9L12", &["g7", "h8", "i9"], &["j10", "f6"]);
        test_three_all_flipped("d4g7h8i9", &["g7", "h8", "i9"], &["j10"]);
        test_three_all_flipped("g7h8i9l12", &["g7", "h8", "i9"], &["f6"]);

        test_three_all_flipped("a1b2c3", &[], &[]);
        test_three_all_flipped("m13n14o15", &[], &[]);

        test_three_all_flipped("a1b2c3d4", &[], &[]);
        test_three_all_flipped("l12m13n14o15", &[], &[]);

        test_three_all_flipped("b2c3d4", &["b2", "c3", "d4"], &["e5"]);
        test_three_all_flipped("l12m13n14", &["l12", "m13", "n14"], &["k11"]);

        test_three_all_flipped("b2c3d4e5", &[], &[]);
        test_three_all_flipped("k11l12m13n14", &[], &[]);

        test_three_all_flipped("b2c3d4f6", &[], &[]);
        test_three_all_flipped("k11l12m13n14", &[], &[]);

        test_three_all_flipped("b2c3d4g7", &[], &[]);
        test_three_all_flipped("i9l12m13n14", &[], &[]);

        test_three_all_flipped("b2c3d4G7", &["b2", "c3", "d4"], &["e5"]);
        test_three_all_flipped("I9l12m13n14", &["l12", "m13", "n14"], &["k11"]);

        test_three_all_flipped("b2c3d4h8", &["b2", "c3", "d4"], &["e5"]);
        test_three_all_flipped("h8l12m13n14", &["l12", "m13", "n14"], &["k11"]);

        test_three_all_flipped("a1", &[], &[]);
        test_three_all_flipped("o1", &[], &[]);
        test_three_all_flipped("a15", &[], &[]);
        test_three_all_flipped("o15", &[], &[]);

        test_three_all_flipped("a14b15", &[], &[]);
        test_three_all_flipped("a1b2", &[], &[]);
        test_three_all_flipped("n1o2", &[], &[]);
        test_three_all_flipped("n14o15", &[], &[]);

        test_three_all_flipped("a13b14c15", &[], &[]);
        test_three_all_flipped("a1b2c3", &[], &[]);
        test_three_all_flipped("m1n2o3", &[], &[]);
        test_three_all_flipped("m13n14o15", &[], &[]);

        test_three_all_flipped("a12b13c14", &[], &[]);
        test_three_all_flipped("b13c14d15", &[], &[]);

        test_three_all_flipped("m2n3o4", &[], &[]);
        test_three_all_flipped("l1m2n3", &[], &[]);

        test_three_all_flipped("g7i9j10", &["g7", "i9", "j10"], &["h8"]);
        test_three_all_flipped("f6g7i9", &["f6", "g7", "i9"], &["h8"]);

        for i in 0..12 {
            test_three_all_transformed_flipped("a1b2c3", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("a1b2c3", &[], &[], |pos| pos + (i, 0).into());

            test_three_all_transformed_flipped("m1n2o3", &[], &[], |pos| pos - (0, i).into());
            test_three_all_transformed_flipped("m1n2o3", &[], &[], |pos| pos + (i, 0).into());
        }

        for i in 0..10 {
            test_three_all_transformed_flipped("b2c3d4", &["b2", "c3", "d4"], &["e5"], |pos| {
                pos + (0, i).into()
            });
            test_three_all_transformed_flipped("b2c3d4", &["b2", "c3", "d4"], &["e5"], |pos| {
                pos + (i, 0).into()
            });
            test_three_all_transformed_flipped(
                "l12m13n14",
                &["l12", "m13", "n14"],
                &["k11"],
                |pos| pos - (0, i).into(),
            );
            test_three_all_transformed_flipped(
                "l12m13n14",
                &["l12", "m13", "n14"],
                &["k11"],
                |pos| pos - (i, 0).into(),
            );
        }

        for i in 0..9 {
            test_three_all_transformed_flipped(
                "c3d4e5",
                &["c3", "d4", "e5"],
                &["b2", "f6"],
                |pos| pos + (0, i).into(),
            );
            test_three_all_transformed_flipped(
                "c3d4e5",
                &["c3", "d4", "e5"],
                &["b2", "f6"],
                |pos| pos + (i, 0).into(),
            );
            test_three_all_transformed_flipped(
                "c3d4e5",
                &["c3", "d4", "e5"],
                &["b2", "f6"],
                |pos| pos + (i, i).into(),
            );

            test_three_all_transformed_flipped("b2c3d4e5", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("c3d4e5f6", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("B2c3d4e5", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("c3d4e5F6", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("b2c3d4e5", &[], &[], |pos| pos + (i, 0).into());
            test_three_all_transformed_flipped("c3d4e5f6", &[], &[], |pos| pos + (i, 0).into());
            test_three_all_transformed_flipped("B2c3d4e5", &[], &[], |pos| pos + (i, 0).into());
            test_three_all_transformed_flipped("c3d4e5F6", &[], &[], |pos| pos + (i, 0).into());

            test_three_all_transformed_flipped("a1c3d4e5", &[], &[], |pos| pos + (0, i).into());
            test_three_all_transformed_flipped("a1c3d4e5", &[], &[], |pos| pos + (i, 0).into());
            test_three_all_transformed_flipped("a1c3d4e5", &[], &[], |pos| pos + (i, i).into());

            test_three_all_transformed_flipped("A1c3d4e5", &["c3", "d4", "e5"], &["f6"], |pos| {
                pos + (0, i).into()
            });
            test_three_all_transformed_flipped("A1c3d4e5", &["c3", "d4", "e5"], &["f6"], |pos| {
                pos + (i, 0).into()
            });
            test_three_all_transformed_flipped("A1c3d4e5", &["c3", "d4", "e5"], &["f6"], |pos| {
                pos + (i, i).into()
            });
        }
    }

    #[test]
    fn test_positions_iter() {
        let board = Board::new();
        let a = board.positions().collect();

        let mut b = HashSet::new();
        for row in 0..board.size() {
            for col in 0..board.size() {
                b.insert(Pos::new(row, col));
            }
        }
        assert_eq!(b, a);
    }

    #[test]
    fn test_squares_iter() {
        let board = Board::new();

        for (_, square) in board.squares() {
            assert_eq!(square, None);
        }
    }

    fn test_four_transformed<F>(board: Board, fours: Board, fives: Board, f: F)
    where
        F: Fn(Pos) -> Pos,
    {
        let board = board.transform(&f);
        let fours = fours.transform(&f);
        let fives: HashSet<Pos> = fives
            .transform(&f)
            .squares()
            .filter(|(_, square)| matches!(square, Some(Side::Black)))
            .map(|(pos, _)| pos)
            .collect();

        for pos in board.positions() {
            let res = board
                .get_fours(pos, Side::Black)
                .into_iter()
                .filter_map(std::convert::identity)
                .flatten()
                .collect();

            if let Some(_) = fours.at(pos) {
                assert_eq!(fives, res);
            } else {
                assert_eq!(res, HashSet::new());
            }
        }
    }

    fn test_four_straight<F>(board: Board, fours: Board, fives: Board, f: F)
    where
        F: Fn(Pos) -> Pos,
    {
        test_four_transformed(board, fours, fives, &f);
        test_four_transformed(board, fours, fives, |pos| f(Pos::transpose(pos)));
    }

    fn test_four_straight_shifted<B>(board: &str, fours: &str, fives: &str, range: B)
    where
        B: IntoIterator<Item = i8>,
    {
        let board = board.parse().unwrap();
        let fours = fours.parse().unwrap();
        let fives = fives.parse().unwrap();
        for shift in range {
            test_four_straight(board, fours, fives, |pos| {
                Pos::new(pos.row(), (pos.col() as i8 + shift) as u8)
            });
        }
    }

    fn check_fours_impl(board: &Board, fours: &Board, fives: &Board) {
        let fives: HashSet<Pos> = fives
            .squares()
            .filter(|(_, square)| matches!(square, Some(Side::Black)))
            .map(|(pos, _)| pos)
            .collect();

        for (pos, square) in fours.squares() {
            let res: HashSet<Pos> = board
                .get_fours(pos, Side::Black)
                .into_iter()
                .filter_map(std::convert::identity)
                .flatten()
                .collect();

            if let Some(_) = square {
                assert_eq!(res, fives);
            } else {
                assert_eq!(res, HashSet::new());
            }
        }
    }

    fn check_fours(board: &Board, fours: &Board, fives: &Board) {
        check_fours_impl(board, fours, fives);
        check_fours_impl(&board.flip(), &fours.flip(), &fives.flip());
    }

    fn test_four_pattern(pattern: &str, len: u8, fours: &str, fives: &str) {
        test_four_pattern_box(pattern, len, RENJU_BOARD_SIZEU8, fours, fives);
    }

    #[test]
    fn test_horiz_fours_none() {
        test_four_pattern("", 0, "", "");
        test_four_pattern("a8", 1, "", "");
        test_four_pattern("a8b8", 2, "", "");
        test_four_pattern("a8b8c8", 3, "", "");
    }

    #[test]
    fn test_horiz_fours_straight() {
        test_four_pattern("b8c8d8e8", 6, "b8c8d8e8", "a8f8");
        test_four_pattern("a8b8c8d8e8", 7, "", "");
        test_four_pattern("a8c8d8e8f8", 7, "c8d8e8f8", "g8");
        test_four_pattern("A8c8d8e8f8", 7, "c8d8e8f8", "b8g8");
        test_four_pattern("A8c8d8e8f8H8", 8, "c8d8e8f8", "b8g8");
    }

    #[test]
    fn test_horiz_fours_degenerate() {
        //test_four_pattern("a8c8d8e8g8", 7, "a8c8d8e8g8", "b8f8");
        //test_four_pattern("a8B8c8d8e8g8", 7, "c8d8e8g8", "f8");
        test_four_pattern("a8B8c8d8e8F8g8", 7, "", "");
        test_four_pattern("a8b8c8d8e8g8", 7, "", "");
        test_four_pattern("a8b8c8d8e8f8g8", 7, "", "");
    }

    #[test]
    fn test_horiz_fours_normal() {
        test_four_pattern("a8c8d8e8", 5, "a8c8d8e8", "b8");
        test_four_pattern("a8B8c8d8e8", 5, "", "");
        test_four_pattern("a8c8d8e8f8", 7, "c8d8e8f8", "g8");

        test_four_pattern("a8b8d8e8f8", 6, "", "");
        test_four_pattern("A8b8d8e8f8", 6, "b8d8e8f8", "c8");

        test_four_pattern("A8b8c8d8e8", 6, "b8c8d8e8", "f8");
        test_four_pattern("A8b8c8d8e8G8", 7, "b8c8d8e8", "f8");
        test_four_pattern("A8b8c8d8e8g8", 7, "", "");

        test_four_pattern("a8b8d8e8", 5, "a8b8d8e8", "c8");
        test_four_pattern("a8b8C8d8e8", 5, "", "");
        test_four_pattern("a8b8c8d8e8", 5, "", "");
    }

    fn test_four_pattern_box(pattern: &str, width: u8, height: u8, fours: &str, fives: &str) {
        let max_col = RENJU_BOARD_SIZEU8 - width;
        let max_row = RENJU_BOARD_SIZEU8 - height;

        let mut board: Board = pattern.parse().unwrap();
        let mut fours: Board = fours.parse().unwrap();
        let mut fives: Board = fives.parse().unwrap();

        let shift_right = |pos: Pos| -> Pos { Pos::new(pos.row(), pos.col() + 1) };
        let shift_down_and_reset =
            |pos: Pos| -> Pos { Pos::new(pos.row() + 1, pos.col() - max_col) };

        for row in 0..=max_row {
            for col in 0..=max_col {
                check_fours(&board, &fours, &fives);
                if col < max_col {
                    board = board.transform(shift_right);
                    fours = fours.transform(shift_right);
                    fives = fives.transform(shift_right);
                }
            }
            if row < max_row {
                board = board.transform(shift_down_and_reset);
                fours = fours.transform(shift_down_and_reset);
                fives = fives.transform(shift_down_and_reset);
            }
        }
    }

    #[test]
    fn test_diag_fours_none() {
        test_four_pattern_box("a1", 1, 1, "", "");
        test_four_pattern_box("a1b2", 2, 2, "", "");
        test_four_pattern_box("a1b2c3", 3, 3, "", "");
    }

    #[test]
    fn test_diag_fours_straight() {
        test_four_pattern_box("b2c3d4e5", 6, 6, "b2c3d4e5", "a1f6");
        test_four_pattern_box("a1b2c3d4e5", 6, 6, "", "");
        test_four_pattern_box("a1b2c3d4e5f6", 6, 6, "", "");

        test_four_pattern_box("A1c3d4e5f6", 7, 7, "c3d4e5f6", "b2g7");
        test_four_pattern_box("A1c3d4e5f6H8", 9, 9, "c3d4e5f6", "b2g7");

        test_four_pattern_box("a1c3d4e5f6", 7, 7, "c3d4e5f6", "g7");
        test_four_pattern_box("a1c3d4e5f6h8", 9, 9, "", "");
    }

    #[test]
    fn test_diag_fours_degenerate() {
        //test_four_pattern_box("a1c3d4e5g7", 7, 7, "a1c3d4e5g7", "b2f6");
        //test_four_pattern_box("a1B2c3d4e5g7", 7, 7, "c3d4e5g7", "f6");
        test_four_pattern_box("a1B2c3d4e5f6g7", 7, 7, "", "");
        test_four_pattern_box("a1b2c3d4e5g7", 7, 7, "", "");
        test_four_pattern_box("a1b2c3d4e5f6g7", 7, 7, "", "");
    }

    #[test]
    fn test_diag_fours_normal() {
        test_four_pattern_box("A1b2c3d4e5", 6, 6, "b2c3d4e5", "f6");
        test_four_pattern_box("A1b2c3d4e5G7", 7, 7, "b2c3d4e5", "f6");
        test_four_pattern_box("A1b2c3d4e5g7", 7, 7, "", "");

        test_four_pattern_box("a1c3d4e5", 5, 5, "a1c3d4e5", "b2");
        test_four_pattern_box("a1B2c3d4e5", 5, 5, "", "");
        test_four_pattern_box("a1b2c3d4e5", 5, 5, "", "");
        test_four_pattern_box("a1c3d4e5f6", 7, 7, "c3d4e5f6", "g7");

        test_four_pattern_box("a1b2d4e5", 5, 5, "a1b2d4e5", "c3");
        test_four_pattern_box("a1b2C3d4e5", 5, 5, "", "");
    }

    fn test_pattern<F>(board: &str, places: &str, f: F)
    where
        F: Fn(&Board, Pos, Side) -> bool,
    {
        let board: Board = board.parse().unwrap();
        let places: Board = places.parse().unwrap();

        for (pos, square) in places.squares() {
            if let Some(side) = square {
                assert_eq!(f(&board, pos, side), true);
                assert_eq!(f(&board, pos, !side), false);
            } else {
                assert_eq!(f(&board, pos, Side::Black), false);
                assert_eq!(f(&board, pos, Side::White), false);
            }
        }
    }

    fn test_win_no_overline(board: &str, five: &str) {
        test_pattern(board, five, Board::is_win_no_overline);
    }

    #[test]
    fn win_no_overline() {
        test_win_no_overline("", "");
        test_win_no_overline("a8", "");
        test_win_no_overline("a8b8", "");
        test_win_no_overline("a8b8c8", "");
        test_win_no_overline("a8b8c8d8", "");
        test_win_no_overline("a8b8c8d8e8", "a8b8c8d8e8");
        test_win_no_overline("a8b8c8d8e8f8", "");
        test_win_no_overline("h8i8j8k8l8", "h8i8j8k8l8");

        test_win_no_overline("b8c8d8e8f8", "b8c8d8e8f8");
    }

    fn test_overline(board: &str, five: &str) {
        test_pattern(board, five, Board::is_overline);
    }

    #[test]
    fn overline() {
        test_overline("a8b8c8d8e8f8", "a8b8c8d8e8f8");
        test_overline("f8g8h8i8j8k8", "f8g8h8i8j8k8");
        test_overline("", "");
        test_overline("a8", "");
        test_overline("a8b8", "");
        test_overline("a8b8c8", "");
        test_overline("a8b8c8d8", "");
        test_overline("a8b8c8d8e8", "");

        test_overline("b8c8d8e8f8", "");
    }

    fn check_forbidden(board: &str, forbidden: &str) {
        let board: Board = board.parse().unwrap();
        let forbidden = forbidden.parse::<PieceBoard<RENJU_BOARD_SIZE>>().unwrap();

        assert_eq!(board.renju_forbidden(), *forbidden.black());
    }

    #[test]
    fn renju_forbidden() {
        check_forbidden("i6g8h8i8h9i9", "h7f9");
        check_forbidden("h11j11f12h12e13k13f14k14c15k15", "i12");
        check_forbidden("g11h11j12j13k13l14m15", "");
        check_forbidden("l2l3l6l8l9", "l5");
        check_forbidden("a2a3a4a8a9a10", "a6");
    }
}
