use anyhow::{bail, Error};
use std::fmt;
use std::ops::Not;
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
    // 18 patterns in total:
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
            0b00000111000,
            0b00001110000,
            0b00011100000,
            0b00011100000,
            0b00001110000,
            0b00000111000,
            0b00000101101,
            0b00010110100,
            0b00101101000,
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
            0b00011000110,
            0b00110001100,
            0b01100011000,
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
            0b00100000001,
            0b01000000010,
            0b10000000100,
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
            Three::Straight(2, 6),
            Three::Straight(3, 7),
            Three::Straight(4, 8),
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
        let border_row = Self::NORMAL_BOUNDARY_BOARD.row(pos.row());

        match Self::get_three_impl(pos.col(), our_row, their_row, border_row) {
            Some(Three::Normal(col)) => Some(Three::Normal(Pos::new(pos.row(), col))),
            Some(Three::Straight(col1, col2)) => Some(Three::Straight(
                Pos::new(pos.row(), col1),
                Pos::new(pos.row(), col2),
            )),
            _ => None,
        }
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

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct Board {
    board0: PieceBoard<RENJU_BOARD_SIZE>, // row major
    board1: PieceBoard<RENJU_BOARD_SIZE>, // column major
}

impl Board {
    const MARGIN: u8 = 12;

    pub const fn new() -> Self {
        Self {
            board0: PieceBoard::new(),
            board1: PieceBoard::new(),
        }
    }

    pub const fn centre(pos: Pos) -> Pos {
        Pos::new(pos.row(), pos.col() + Self::MARGIN)
    }

    pub const fn decentre(pos: Pos) -> Pos {
        Pos::new(pos.row(), pos.col() - Self::MARGIN)
    }

    pub const fn set(mut self, pos: Pos, val: Option<Side>) -> Self {
        self.board0 = self.board0.set(Self::centre(pos), val);
        self.board1 = self.board1.set(Self::centre(pos.transpose()), val);
        self
    }

    pub const fn at(&self, pos: Pos) -> Option<Side> {
        let pos = Self::centre(pos);

        self.board0.at(pos)
    }

    pub fn get_threes(&self, pos: Pos, side: Side) -> [Option<Three<Pos>>; 4] {
        [
            self.board0
                .get_three(Self::centre(pos), side)
                .map(|x| x.map(Self::decentre)),
            self.board1
                .get_three(Self::centre(pos.transpose()), side)
                .map(|x| x.map(Self::decentre).map(Pos::transpose)),
            None,
            None,
        ]
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
                board = board.set(Self::centre(pos), false);
                col += 1;
            }
            row += 1;
        }
        board
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
    use crate::board::{BitBoard, Board, PieceBoard, Side, Three, RENJU_BOARD_SIZEU8};
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

        let board: PieceBoard<15> = b.parse().unwrap();
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

        //board.check_self();
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
    fn straight_three() {
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
        //TODO vertical three tests
    }
}
