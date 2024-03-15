use std::ops::{BitXor, Not};
use std::str;
use std::fmt;

/// An renju board implementation

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Side {
    Black,
    White,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Square {
    Empty,
    Piece(Side),
}

impl Not for Side {
    type Output = Side;

    fn not(self) -> Self::Output {
        match self {
            Self::Black => Self::White,
            Self::White => Self::Black,
        }
    }
}

pub struct BoardIter<'a, B: Board> {
    board: &'a B,
    row: usize,
    col: usize,
}

impl<'a, B: Board> Iterator for BoardIter<'a, B> {
    type Item = B::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.row > self.board.size() {
            None
        } else {
            let item = self.board.at(self.row, self.col);
            self.row += 1;
            todo!()
        }
    }
}

pub trait Board: Default {
    type Item: Copy;

    fn at(&self, row: usize, col: usize) -> Self::Item;
    fn set(&mut self, row: usize, col: usize, val: Self::Item);
    fn size(&self) -> usize;

    /// WARNING: this functions should only be used for debugging purposes as it is not optimized
    fn transpose(&self) -> Self {
        let mut res = Self::default();

        for row in 0..self.size() {
            for col in 0..self.size() {
                res.set(col, row, self.at(row, col))
            }
        }
        res
    }

    fn is_oob(&self, row: usize, col: usize) -> bool {
        row >= self.size() || col >= self.size()
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
struct BitBoard<const SIZE: usize> {
    rows: [u32; SIZE],
}

impl<const SIZE: usize> BitXor for BitBoard<SIZE> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let mut rows = self.rows;

        for i in 0..SIZE {
            rows[i] ^= rhs.row(i);
        }

        Self { rows }
    }
}

impl<const SIZE: usize> Default for BitBoard<SIZE> {
    fn default() -> Self {
        Self { rows: [0; SIZE] }
    }
}

impl<const SIZE: usize> Board for BitBoard<SIZE> {
    type Item = bool;

    fn at(&self, row: usize, col: usize) -> Self::Item {
        (self.row(row) & (1 << col)) != 0
    }

    fn set(&mut self, row: usize, col: usize, val: Self::Item) {
        let bit = (val as u32) << col;
        self.rows[row] = (self.row(row) & !bit) | bit;
    }

    fn size(&self) -> usize {
        SIZE
    }
}

impl<const SIZE: usize> BitBoard<SIZE> {
    pub const fn row(&self, row: usize) -> u32 {
        self.rows[row]
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct PieceBoard<const SIZE: usize> {
    pieces: BitBoard<SIZE>,
    black: BitBoard<SIZE>,
}

impl<const SIZE: usize> Default for PieceBoard<SIZE> {
    fn default() -> Self {
        Self {
            pieces: Default::default(),
            black: Default::default(),
        }
    }
}

impl<const SIZE: usize> Board for PieceBoard<SIZE> {
    type Item = Square;

    fn at(&self, row: usize, col: usize) -> Self::Item {
        let has_piece = !self.pieces.at(row, col);
        let is_black = self.black.at(row, col);

        debug_assert!(!(is_black && !has_piece));
        match (has_piece, is_black) {
            (true, true) => Square::Piece(Side::Black),
            (true, false) => Square::Piece(Side::White),
            _ => Square::Empty,
        }
    }

    fn set(&mut self, row: usize, col: usize, val: Self::Item) {
        self.pieces.set(row, col, val != Square::Empty);
        self.black.set(row, col, val == Square::Piece(Side::Black));
    }

    fn size(&self) -> usize {
        SIZE
    }
}

const THREE_PATTERNS: &'static [u32] = &[0b001110, 0b011100, 0b011010, 0b010110];

impl<const SIZE: usize> PieceBoard<SIZE> {
    fn get_row(&self, row: usize, side: Side) -> u32 {
        match side {
            Side::Black => self.black.row(row),
            Side::White => self.black.row(row) ^ self.pieces.row(row),
        }
    }
    // types of threes:
    // b = our piece
    // . = empty square
    //
    // 1) . . b b b .
    // 2) . b b b . .
    // 3) . b b . b .
    // 4) . b . b b .
    //
    //
    // xxx
    // xxx
    // xxx
    //
    // It is impossible to get a double three on a single row with one move. Even with overline
    // allowed
    // TODO prove by exhaustion
    pub fn is_three(&self, row: usize, col: usize, side: Side) -> bool {
        // TODO try branchless variant with accumulator return
        // i.e.:
        // let mut res = false;
        // ...
        // if is_three && !opposing_piece_in_window {
        //  res = true
        //  continue
        // }
        let max = (col + 6).min(SIZE);
        let min = col.saturating_sub(6);

        let our_row = self.get_row(row, side);
        let their_row = self.get_row(row, !side);

        for shift in min..max {
            let mask = 0b111111 << shift;

            // If an opposing piece is in the current 6-square window, then it cannot be a three
            // for this side
            if (their_row & mask) != 0 {
                continue;
            }

            // TODO check if hand made loop is better optimized than lazy iterators
            if THREE_PATTERNS
                .iter()
                .any(|&pattern| (((our_row & mask) >> shift) ^ pattern) == 0)
            {
                return true;
            }
        }
        false
    }
}


trait BoardRotation: Default {}
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct BoardRotationRight45;
impl BoardRotation for BoardRotationRight45 {}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
struct DiagonalBoard<const DIAG_SIZE: usize, R: BoardRotation> {
    board: PieceBoard<DIAG_SIZE>,
    _rot: core::marker::PhantomData<R>,
}

impl<const DIAG_SIZE: usize> Board for DiagonalBoard<DIAG_SIZE, BoardRotationRight45> {
    type Item = Square;

    fn at(&self, row: usize, col: usize) -> Self::Item {
        let (row, col) = self.transform(row, col);
        self.board.at(row, col)
    }

    fn set(&mut self, row: usize, col: usize, val: Self::Item) {
        let (row, col) = self.transform(row, col);
        self.board.set(row, col, val)
    }

    fn size(&self) -> usize {
        (DIAG_SIZE + 1) / 2
    }
}

impl<const DIAG_SIZE: usize, R> DiagonalBoard<DIAG_SIZE, R>
where
    R: BoardRotation,
    DiagonalBoard<DIAG_SIZE, R>: Board,
{
    fn transform(&self, row: usize, col: usize) -> (usize, usize) {
        (row + col, Board::size(self) - (row + col))
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct HorizontalBoard<const SIZE: usize> {
    board: PieceBoard<SIZE>,
}

impl<const SIZE: usize> Board for HorizontalBoard<SIZE> {
    type Item = <PieceBoard<SIZE> as Board>::Item;

    fn at(&self, row: usize, col: usize) -> Self::Item {
        self.board.at(row, col)
    }

    fn set(&mut self, row: usize, col: usize, val: Self::Item) {
        self.board.set(row, col, val)
    }

    fn size(&self) -> usize {
        SIZE
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub struct GameBoard<const SIZE: usize> {
    board0: HorizontalBoard<SIZE>,
}

impl<const SIZE: usize> fmt::Debug for GameBoard<SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in 0..SIZE {
            for col in 0..SIZE {
                match self.board0.at(row, col) {
                    Square::Empty => write!(f, ".")?,
                    Square::Piece(Side::Black) => write!(f, "b")?,
                    Square::Piece(Side::White) => write!(f, "w")?,
                }
                write!(f, " ")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<const SIZE: usize> Board for GameBoard<SIZE> {
    type Item = Square;

    fn at(&self, row: usize, col: usize) -> Self::Item {
        self.board0.at(row, col)
    }

    fn set(&mut self, row: usize, col: usize, val: Self::Item) {
        self.board0.set(row, col, val);
    }

    fn size(&self) -> usize {
        SIZE
    }
}

#[derive(Copy, Clone, Debug)]
pub enum ParseGameBoardError {
    NotAscii(usize),
    NotAlpha(usize),
    InvalidNum(usize),
    OOB(usize, usize, usize),
    DoublePlace(usize, usize, usize, Side),
}

impl<const SIZE: usize> str::FromStr for GameBoard<SIZE> {
    type Err = ParseGameBoardError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut board = Self::default();
        let mut iter = s.chars().peekable();
        let mut cursor = 1;

        while let Some(ch) = iter.next() {
            let start = cursor;

            if !ch.is_ascii() {
                return Err(ParseGameBoardError::NotAscii(start));
            }

            if !ch.is_ascii_alphabetic() {
                return Err(ParseGameBoardError::NotAlpha(start));
            }

            let side = if ch.is_ascii_lowercase() {
                Side::Black
            } else {
                Side::White
            };
            let col = ch.to_ascii_lowercase() as usize - 'a' as usize;

            let mut has_row = false;
            let mut row: usize = 0;

            while let Some(digit) = iter.peek().and_then(|x| x.to_digit(10)) {
                has_row = true;
                row = row
                    .checked_mul(10)
                    .ok_or(ParseGameBoardError::InvalidNum(start))?;
                row = row
                    .checked_add(digit as usize)
                    .ok_or(ParseGameBoardError::InvalidNum(start))?;

                cursor += 1;
            }

            if !has_row {
                return Err(ParseGameBoardError::InvalidNum(cursor));
            }

            if board.is_oob(row, col) {
                return Err(ParseGameBoardError::OOB(start, row, col));
            }

            if let Square::Piece(side) = board.at(row, col) {
                return Err(ParseGameBoardError::DoublePlace(start, row, col, side));
            }

            board.set(row, col, Square::Piece(side));
            cursor += 1;
        }

        Ok(board)
    }
}

#[cfg(test)]
mod tests {
    use super::{GameBoard, Square, Board, BitBoard};

    #[test]
    fn empty_bitboard() {
        let board: BitBoard<19> = Default::default();
    }

    #[test]
    fn parse_board() {
        let board: GameBoard<19>  = "".parse().unwrap();

        println!("{:?}", board);
        for row in 0..19 {
            for col in 0..19 {
                assert_eq!(board.at(row, col), Square::Empty);
            }
        }
    }
}
