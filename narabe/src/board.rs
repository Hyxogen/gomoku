use crate::table::*;
use anyhow::{bail, Error};
#[cfg(test)]
use std::collections::HashMap;
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
    const MARGIN: u8 = 12;

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
    pub fn gen_table<F: Fn(Pos) -> Pos>(f: F) {
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
        print!("const TRANSFORM_TABLE: &'static [&'static [Pos]] = &[");

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

        println!("const INVERSE_TABLE: &'static [&'static [Pos]] = &[");
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
    use crate::table::*;
    use anyhow::Result;
    use std::collections::HashSet;
    use tools::{DeltaPos, Pos};

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
}
