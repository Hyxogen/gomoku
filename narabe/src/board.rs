use anyhow::{bail, Error};
use std::fmt;
/// 15x15 Renju board
use std::ops::Not;
use std::str;
use tools::Pos;

const BOARD_SIZE: usize = 15;
const DIAG_SIZE: usize = (BOARD_SIZE * 2) - 1;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Side {
    Black,
    White,
}

impl Not for Side {
    type Output = Side;

    fn not(self) -> Self::Output {
        match self {
            Side::Black => Side::White,
            Side::White => Side::Black,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Square {
    Empty,
    Piece(Side),
}

pub struct BitBoard<const SIZE: usize> {
    rows: [u32; SIZE],
}

impl<const SIZE: usize> fmt::Debug for BitBoard<SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in 0..SIZE {
            for col in 0..SIZE {
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

// TODO check if passing row and col by u8 might be faster
impl<const SIZE: usize> BitBoard<SIZE> {
    pub fn new() -> Self {
        Self { rows: [0; SIZE] }
    }

    pub fn row(&self, row: usize) -> u32 {
        self.rows[row]
    }

    pub fn at(&self, pos: Pos) -> bool {
        debug_assert!(pos.col() < SIZE);
        (self.rows[pos.row()] & (1 << pos.col())) != 0
    }

    pub fn set(&mut self, pos: Pos, val: bool) {
        debug_assert!(pos.col() < SIZE);
        let mask = 1 << pos.col();
        self.rows[pos.row()] = (self.rows[pos.row()] & !mask) | val.then_some(mask).unwrap_or(0);
    }
}

pub struct PieceBoard<const SIZE: usize> {
    pieces: BitBoard<SIZE>,
    black: BitBoard<SIZE>,
}

impl<const SIZE: usize> fmt::Debug for PieceBoard<SIZE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "    ")?;
        for col in 0..SIZE {
            if col < 10 {
                write!(f, "{}", (col as u8 + '0' as u8) as char)?;
            } else {
                write!(f, "{}", ((col - 10) as u8 + 'a' as u8) as char)?;
            }
            write!(f, " ")?;
        }
        writeln!(f)?;

        for row in 0..SIZE {
            write!(f, "{:0>2}) ", row)?;
            for col in 0..SIZE {
                match self.at(Pos::new(row, col)) {
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
// It is impossible to get a double three on a single row with one move. Even with overline
// allowed
// *TODO prove by exhaustion
//
const HORIZONTAL_THREE_PATTERNS: &'static [u32] = &[0b001110, 0b011100, 0b011010, 0b010110];
const DIAGONAL_THREE_PATTERNS: &'static [u32] = &[
    0b000001010100,
    0b000101010000,
    0b000101000100,
    0b000100010100,
];

// types of fours:
// b = our piece
// . = empty square
//
// 1) . b b b b
// 2) b b b b .
// can probably trim the edges of the end of the four patterns as they should be zero anyway
const HORIZONTAL_FOUR_PATTERNS: &'static [u32] = &[0b01111, 0b11110, 0b10111, 0b11101, 0b11011];
const DIAGONAL_FOUR_PATTERNS: &'static [u32] = &[
    0b0010101010,
    0b010110100,
    0b0100010101,
    0b0101010001,
    0b0101000101,
];

const HORIZONTAL_WIN_PATTERNS: &'static [u32] = &[0b11111];
const DIAGONAL_WIN_PATTERNS: &'static [u32] = &[0b0101010101];

const HORIZONTAL_OVERLINE_PATTERNS: &'static [u32] = &[0b111111];
const DIAGONAL_OVERLINE_PATTERNS: &'static [u32] = &[0b010101010101];

impl<const SIZE: usize> PieceBoard<SIZE> {
    pub fn new() -> Self {
        Self {
            pieces: BitBoard::new(),
            black: BitBoard::new(),
        }
    }

    pub fn at(&self, pos: Pos) -> Square {
        let has_piece = self.pieces.at(pos);
        let is_black = self.black.at(pos);

        debug_assert!(!(is_black && !has_piece));
        match (has_piece, is_black) {
            (true, true) => Square::Piece(Side::Black),
            (true, false) => Square::Piece(Side::White),
            _ => Square::Empty,
        }
    }

    pub fn set(&mut self, pos: Pos, val: Square) {
        self.pieces.set(pos, val != Square::Empty);
        self.black.set(pos, val == Square::Piece(Side::Black));
    }

    pub fn pieces(&self) -> &BitBoard<SIZE> {
        &self.pieces
    }

    pub fn black(&self) -> &BitBoard<SIZE> {
        &self.black
    }

    fn get_row(&self, row: usize, side: Side) -> u32 {
        match side {
            Side::Black => self.black.row(row),
            Side::White => self.pieces.row(row) ^ self.black.row(row),
        }
    }

    pub fn count_pattern<const LEN: usize, const NO_OPPOSING: bool>(
        &self,
        pos: Pos,
        side: Side,
        patterns: &[u32],
    ) -> u8 {
        // TODO try branchless variant with accumulator return
        // i.e.:
        // let mut res = false;
        // ...
        // if is_three && !opposing_piece_in_window {
        //  res = true
        //  continue
        // }
        debug_assert!(LEN <= SIZE);
        debug_assert!(LEN > 0);
        let mut count = 0;

        let max = (pos.col()).min(SIZE - LEN);
        let min = pos.col().saturating_sub(LEN - 1);

        let our_row = self.get_row(pos.row(), side);
        let their_row = self.get_row(pos.row(), !side);

        for shift in min..=max {
            let mask = ((1 << LEN) - 1) << shift;

            if NO_OPPOSING && (their_row & mask) != 0 {
                continue;
            }

            // TODO check if hand made loop is better optimized than lazy iterators
            count += patterns
                .iter()
                .filter(|&pattern| (((our_row & mask) >> shift) ^ pattern) == 0)
                .count() as u8;
        }
        count
    }

    pub fn has_pattern<const LEN: usize, const NO_OPPOSING: bool>(
        &self,
        pos: Pos,
        side: Side,
        patterns: &[u32],
    ) -> bool {
        self.count_pattern::<LEN, NO_OPPOSING>(pos, side, patterns) > 0
    }
}

pub struct Board {
    //Row Major
    board0: PieceBoard<BOARD_SIZE>,
    //Column Major
    board1: PieceBoard<BOARD_SIZE>,

    //Left Bottom to Right Top
    board2: PieceBoard<DIAG_SIZE>,
    //Left Top to Right Bottom
    board3: PieceBoard<DIAG_SIZE>,
}

impl fmt::Debug for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Row Major")?;
        writeln!(f, "{:?}", self.board0)?;

        writeln!(f, "Column Major")?;
        writeln!(f, "{:?}", self.board1)?;

        writeln!(f, "Left Bottom to Right Top")?;
        writeln!(f, "{:?}", self.board2)?;

        writeln!(f, "Left Top to Right Bottom")?;
        writeln!(f, "{:?}", self.board3)
    }
}

impl Board {
    pub fn new() -> Self {
        Board {
            board0: PieceBoard::new(),
            board1: PieceBoard::new(),
            board2: PieceBoard::new(),
            board3: PieceBoard::new(),
        }
    }

    pub fn at(&self, pos: Pos) -> Square {
        self.board0.at(pos)
    }

    pub fn rot_right(pos: Pos) -> Pos {
        Self::rot_left(pos).transpose()
    }

    //https://math.stackexchange.com/a/733222
    pub fn rot_left(pos: Pos) -> Pos {
        Pos::new(
            pos.row() + pos.col(),
            (BOARD_SIZE - 1) - pos.row() + pos.col(),
        )
    }

    pub fn set(&mut self, pos: Pos, val: Square) {
        self.board0.set(pos, val);
        self.board1.set(pos.transpose(), val);
        self.board2.set(Self::rot_right(pos), val);
        self.board3.set(Self::rot_left(pos), val);
    }

    pub fn is_oob(&self, pos: Pos) -> bool {
        pos.row() >= BOARD_SIZE || pos.col() >= BOARD_SIZE
    }

    pub fn is_free(&self, pos: Pos) -> bool {
        self.at(pos) == Square::Empty
    }

    pub fn row_major(&self) -> &PieceBoard<BOARD_SIZE> {
        &self.board0
    }

    pub fn check_self(&self) {
        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                let pos = Pos::new(row, col);
                let val = self.board0.at(pos);

                assert_eq!(self.board1.at(pos.transpose()), val);
                assert_eq!(self.board2.at(Self::rot_right(pos)), val);
                assert_eq!(self.board3.at(Self::rot_left(pos)), val);
            }
        }
    }

    pub fn is_overline(&self, pos: Pos, side: Side) -> bool {
        self.board0
            .has_pattern::<6, false>(pos, side, HORIZONTAL_OVERLINE_PATTERNS)
            || self.board1.has_pattern::<6, false>(
                pos.transpose(),
                side,
                HORIZONTAL_OVERLINE_PATTERNS,
            )
            || self.board2.has_pattern::<12, false>(
                Self::rot_right(pos),
                side,
                DIAGONAL_OVERLINE_PATTERNS,
            )
            || self.board3.has_pattern::<12, false>(
                Self::rot_left(pos),
                side,
                DIAGONAL_OVERLINE_PATTERNS,
            )
    }

    pub fn is_win(&self, pos: Pos, side: Side) -> bool {
        self.board0
            .has_pattern::<5, false>(pos, side, HORIZONTAL_WIN_PATTERNS)
            || self
                .board1
                .has_pattern::<5, false>(pos.transpose(), side, HORIZONTAL_WIN_PATTERNS)
            || self.board2.has_pattern::<10, false>(
                Self::rot_right(pos),
                side,
                DIAGONAL_WIN_PATTERNS,
            )
            || self.board3.has_pattern::<10, false>(
                Self::rot_left(pos),
                side,
                DIAGONAL_WIN_PATTERNS,
            )
    }

    pub fn is_double_three(&self, pos: Pos, side: Side) -> bool {
        self.count_threes(pos, side) >= 2
    }

    pub fn count_threes(&self, pos: Pos, side: Side) -> u8 {
        if self.board0.at(pos) != Square::Piece(side) {
            return 0;
        }

        let mut three_count = 0;

        if self
            .board0
            .has_pattern::<6, true>(pos, side, HORIZONTAL_THREE_PATTERNS)
        {
            three_count += 1;
        }

        if self
            .board1
            .has_pattern::<6, true>(pos.transpose(), side, HORIZONTAL_THREE_PATTERNS)
        {
            three_count += 1;
        }

        if self
            .board2
            .has_pattern::<12, true>(Self::rot_right(pos), side, DIAGONAL_THREE_PATTERNS)
        {
            three_count += 1;
        }

        if self
            .board3
            .has_pattern::<12, true>(Self::rot_left(pos), side, DIAGONAL_THREE_PATTERNS)
        {
            three_count += 1;
        }

        three_count
    }

    pub fn is_double_four(&self, pos: Pos, side: Side) -> bool {
        self.count_fours(pos, side) >= 2
    }

    pub fn count_fours(&self, pos: Pos, side: Side) -> u8 {
        if self.board0.at(pos) != Square::Piece(side) {
            return 0;
        }

        let mut count = 0;

        count += self
            .board0
            .count_pattern::<5, true>(pos, side, HORIZONTAL_FOUR_PATTERNS);

        count +=
            self.board1
                .count_pattern::<5, true>(pos.transpose(), side, HORIZONTAL_FOUR_PATTERNS);

        count += self.board2.count_pattern::<10, true>(
            Self::rot_right(pos),
            side,
            DIAGONAL_FOUR_PATTERNS,
        );

        count += self.board3.count_pattern::<10, true>(
            Self::rot_left(pos),
            side,
            DIAGONAL_FOUR_PATTERNS,
        );

        count
    }

    pub const fn size(&self) -> usize {
        15
    }

    pub const fn left_right(&self) -> &PieceBoard<BOARD_SIZE> {
        &self.board0
    }

    pub const fn top_bot(&self) -> &PieceBoard<BOARD_SIZE> {
        &self.board1
    }

    pub const fn bot_left_top_right(&self) -> &PieceBoard<DIAG_SIZE> {
        &self.board2
    }

    pub const fn top_left_bot_right(&self) -> &PieceBoard<DIAG_SIZE> {
        &self.board3
    }
}

impl str::FromStr for Board {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.is_ascii() {
            bail!("not ascii");
        }

        let mut board = Board::new();
        let mut iter = s.chars().peekable();

        while let Some(ch) = iter.next() {
            if !ch.is_ascii_alphabetic() {
                bail!("not alpabetic");
            }

            let side = if ch.is_ascii_lowercase() {
                Side::Black
            } else {
                Side::White
            };
            let col = ch.to_ascii_lowercase() as usize - 'a' as usize;

            let mut got_digit = false;
            let mut row: usize = 0;

            while let Some(digit) = iter.peek().and_then(|x| x.to_digit(10)) {
                got_digit = true;
                row = row.checked_mul(10).ok_or(Error::msg("number too large"))?;
                row = row
                    .checked_add(digit as usize)
                    .ok_or(Error::msg("number too large"))?;

                iter.nth(0);
            }

            if !got_digit {
                bail!("no row specified");
            }

            if row == 0 {
                bail!("row must be > 0");
            }

            let pos = Pos::new(row - 1, col);

            if board.is_oob(pos) {
                bail!("out of bounds");
            }

            if !board.is_free(pos) {
                bail!("already piece on pos {} ", pos);
            }

            board.set(pos, Square::Piece(side));
        }
        Ok(board)
    }
}

impl fmt::Display for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                let pos = Pos::new(row, col);

                if let Square::Piece(side) = self.at(pos) {
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
    use super::{
        BitBoard, Board, PieceBoard, Pos, Side, Square, BOARD_SIZE, DIAGONAL_THREE_PATTERNS,
        HORIZONTAL_THREE_PATTERNS,
    };
    use anyhow::Result;
    use std::str::FromStr;

    #[test]
    fn empty_board() {
        let board = Board::new();

        board.check_self();
        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                assert!(board.is_free((row, col).into()));
            }
        }
    }

    #[test]
    fn parse_empty_board() {
        let board: Board = "".parse().unwrap();

        board.check_self();
        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                assert!(board.is_free((row, col).into()));
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
        assert_eq!(board.at(b.parse().unwrap()), Square::Piece(side));
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
        let board: Board = "g7N4c7E12i4E2i9G9e6g6".parse()?;

        assert_eq!(board.at("g7".parse()?), Square::Piece(Side::Black));
        assert_eq!(board.at("n4".parse()?), Square::Piece(Side::White));
        assert_eq!(board.at("c7".parse()?), Square::Piece(Side::Black));
        assert_eq!(board.at("e12".parse()?), Square::Piece(Side::White));
        assert_eq!(board.at("i4".parse()?), Square::Piece(Side::Black));
        assert_eq!(board.at("e2".parse()?), Square::Piece(Side::White));
        assert_eq!(board.at("i9".parse()?), Square::Piece(Side::Black));
        assert_eq!(board.at("g9".parse()?), Square::Piece(Side::White));
        assert_eq!(board.at("e6".parse()?), Square::Piece(Side::Black));
        assert_eq!(board.at("e6".parse()?), Square::Piece(Side::Black));
        Ok(())
    }

    #[test]
    fn place_single() {
        let mut board = Board::new();

        board.set(Pos::new(0, 0), Square::Piece(Side::Black));
        board.check_self();

        let mut board = Board::new();

        board.set(Pos::new(0, 1), Square::Piece(Side::White));
        board.check_self();

        let mut board = Board::new();
        board.set(Pos::new(1, 0), Square::Piece(Side::White));
        board.check_self();
    }

    #[test]
    fn place_everywhere_once() {
        let mut side = Side::Black;

        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                let mut board = Board::new();
                board.set((row, col).into(), Square::Piece(side));
                board.check_self();

                side = !side;
            }
        }
    }

    #[test]
    fn double_three_horiz_vert() -> Result<()> {
        let board: Board = "h11h10j8k8h8".parse()?;

        assert_eq!(board.is_double_three("h8".parse()?, Side::Black), true);
        assert_eq!(board.is_double_three("h11".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("h10".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("j8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("k8".parse()?, Side::Black), false);
        Ok(())
    }

    #[test]
    fn double_three_diag_horiz() -> Result<()> {
        let board: Board = "h8i8j8f10e11".parse()?;

        assert_eq!(board.is_double_three("h8".parse()?, Side::Black), true);
        assert_eq!(board.is_double_three("i8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("j8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("f10".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("e11".parse()?, Side::Black), false);
        Ok(())
    }

    #[test]
    fn allow_four_three() -> Result<()> {
        let board: Board = "j8k8h10h11h12h8".parse()?;

        // h8 is not a double three, placing a black stone on h8 will make a four and a three at
        // the same time, which is allowed
        assert_eq!(board.is_double_three("h8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("j8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("k8".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("h10".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("h11".parse()?, Side::Black), false);
        assert_eq!(board.is_double_three("h12".parse()?, Side::Black), false);
        Ok(())
    }

    #[test]
    fn diagonal_three() -> Result<()> {
        let board: Board = "f10g9h8".parse()?;
        let diag_board = board.top_left_bot_right();

        assert_eq!(
            diag_board.has_pattern::<12, true>(
                Board::rot_left("f10".parse()?),
                Side::Black,
                DIAGONAL_THREE_PATTERNS
            ),
            true
        );
        assert_eq!(
            diag_board.has_pattern::<12, true>(
                Board::rot_left("g9".parse()?),
                Side::Black,
                DIAGONAL_THREE_PATTERNS
            ),
            true
        );
        assert_eq!(
            diag_board.has_pattern::<12, true>(
                Board::rot_left("h8".parse()?),
                Side::Black,
                DIAGONAL_THREE_PATTERNS
            ),
            true
        );
        Ok(())
    }

    #[test]
    fn incorrect_three() -> Result<()> {
        let board: Board = "h4h5h6h8".parse()?;
        let board = board.top_bot();

        assert_eq!(
            board.has_pattern::<6, true>(
                Pos::from_str("h8")?.transpose(),
                Side::Black,
                HORIZONTAL_THREE_PATTERNS
            ),
            false
        );
        Ok(())
    }

    #[test]
    fn double_four() -> Result<()> {
        let board: Board = "h8i8j8k8h9h10h11".parse()?;

        assert_eq!(board.is_double_four("h8".parse()?, Side::Black), true);
        Ok(())
    }

    #[test]
    fn win_positions() -> Result<()> {
        let board: Board = "f8g8h8i8j8k8".parse()?;

        assert_eq!(board.is_win("f8".parse()?, Side::Black), true);
        assert_eq!(board.is_win("g8".parse()?, Side::Black), true);
        assert_eq!(board.is_win("h8".parse()?, Side::Black), true);
        assert_eq!(board.is_win("i8".parse()?, Side::Black), true);
        assert_eq!(board.is_win("j8".parse()?, Side::Black), true);
        assert_eq!(board.is_win("k8".parse()?, Side::Black), true);
        Ok(())
    }

    #[test]
    fn double_four_one_diag_line() -> Result<()> {
        let board: Board = "d5f7h9j11g8".parse()?;

        assert_eq!(board.is_double_four("g8".parse()?, Side::Black), true);
        Ok(())
    }

    #[test]
    fn double_four_one_horiz_line() -> Result<()> {
        let board: Board = "e8g8h8i8k8".parse()?;

        assert_eq!(board.is_double_four("h8".parse()?, Side::Black), true);
        Ok(())
    }

    #[test]
    fn place_and_remove_bitboard() {
        let mut board: BitBoard<15> = BitBoard::new();

        let pos = Pos::new(4, 6);
        board.set(pos, true);
        assert_eq!(board.at(pos), true);

        board.set(pos, false);
        assert_eq!(board.at(pos), false);
    }

    #[test]
    fn place_and_remove() {
        let mut board: PieceBoard<15> = PieceBoard::new();

        let pos = Pos::new(4, 6);
        board.set(pos, Square::Piece(Side::Black));
        assert_eq!(board.at(pos), Square::Piece(Side::Black));

        board.set(pos, Square::Empty);
        assert_eq!(board.at(pos), Square::Empty);
    }
}
