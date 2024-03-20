use crate::table::*;
use anyhow::{bail, Error};
use std::collections::HashMap;
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

pub const fn set_bit(row: u32, idx: usize, val: bool) -> u32 {
    let mask = 1 << idx;
    let b = if val { mask } else { 0 };

    (row & !mask) | b
}

// TODO check if passing row and col by u8 might be faster
impl<const SIZE: usize> BitBoard<SIZE> {
    pub const fn new() -> Self {
        Self { rows: [0; SIZE] }
    }

    pub const fn filled() -> Self {
        Self {
            rows: [u32::MAX; SIZE],
        }
    }

    pub const fn not(mut self) -> Self {
        let mut i = 0;

        while i < SIZE {
            self.rows[i] = !self.rows[i];
            i += 1;
        }
        self
    }

    pub const fn row(&self, row: usize) -> u32 {
        self.rows[row]
    }

    pub const fn at(&self, pos: Pos) -> bool {
        debug_assert!(pos.col() < SIZE);
        (self.rows[pos.row()] & (1 << pos.col())) != 0
    }

    pub fn set(&mut self, pos: Pos, val: bool) {
        debug_assert!(pos.col() < SIZE);
        self.rows[pos.row()] = set_bit(self.rows[pos.row()], pos.col(), val);
    }

    pub const fn set_move(mut self, pos: Pos, val: bool) -> Self {
        self.rows[pos.row()] = set_bit(self.rows[pos.row()], pos.col(), val);
        self
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

const NORMAL_BOUNDARY: &'static BitBoard<BOARD_SIZE> = &Board::normal_boundary_board();
const DIAGONAL_BOUNDARY: &'static BitBoard<DIAG_SIZE> = &Board::diag_boundary_board();

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

    //Will return the position to place for straight for if it is a three
    pub fn get_three(&self, pos: Pos, side: Side) -> Option<Pos> {
        if SIZE == BOARD_SIZE {
            self.has_three_horizontal(pos, side)
        } else {
            self.has_three_diagonal(pos, side)
        }
    }

    fn is_pattern(&self, pos: Pos, side: Side, pattern: u32, len: usize) -> bool {
        let max = (pos.col()).min(SIZE - len);
        let min = pos.col().saturating_sub(len - 1);

        let our_row = self.get_row(pos.row(), side);
        for shift in min..=max {
            let shifted = pattern << shift;

            if (our_row & shifted) == shifted {
                return true;
            }
        }
        false
    }

    pub fn is_overline(&self, pos: Pos, side: Side) -> bool {
        self.is_pattern(pos, side, 0b111111, 6)
    }

    pub fn is_win(&self, pos: Pos, side: Side) -> bool {
        self.is_pattern(pos, side, 0b11111, 5)
    }

    // NOTE: this function will probably falsely report a five as a three. This should probably not be a
    // problem anywhere
    fn has_three_horizontal(&self, pos: Pos, side: Side) -> Option<Pos> {
        //detect threes by checking if one piece away from straight four (similar how fours
        //are detected)
        debug_assert!(SIZE == BOARD_SIZE);
        let mask_len = 6;

        let max = (pos.col()).min(SIZE - mask_len);
        let min = pos.col().saturating_sub(mask_len - 1);

        let our_row = self.get_row(pos.row(), side);
        let their_row = self.get_row(pos.row(), !side);
        //println!("");

        for shift in min..=max {
            //TODO might be better to shift our_row >> shift, instead of all others
            let four = 0b011110 << shift;
            let four_mask = 0b111111 << shift;
            let overline_mask = 0b10000001u32.wrapping_shl((shift as u32).saturating_sub(1));

            let missing = (our_row & four_mask) ^ four;

            if (their_row & four_mask) == 0
                && (our_row & overline_mask) == 0
                && missing.count_ones() == 1
            {
                return Some(Pos::new(pos.row(), missing.trailing_zeros() as usize));
            }
        }
        None
    }

    //if some, returns the position for the straight four
    //NOTE, the the position will have to be untransformed
    fn has_three_diagonal(&self, pos: Pos, side: Side) -> Option<Pos> {
        debug_assert!(SIZE == DIAG_SIZE);
        let mask_len = 12;

        let max = (pos.col()).min(SIZE - mask_len);
        let min = pos.col().saturating_sub(mask_len - 1);

        let our_row = self.get_row(pos.row(), side);
        let their_row = self.get_row(pos.row(), !side);
        let border_row = DIAGONAL_BOUNDARY.row(pos.row());

        for shift in min..=max {
            let four = 0b011110 << shift;
            let four_mask = 0b111111 << shift;
            let overline_mask = 0b10000001u32.wrapping_shl((shift as u32).saturating_sub(1));

            let missing = (our_row & four_mask) ^ four;

            if (their_row & four_mask) == 0
                && (border_row & four_mask) == 0
                && (our_row & overline_mask) == 0
                && missing.count_ones() == 1
            {
                return Some(Pos::new(pos.row(), missing.trailing_zeros() as usize));
            }
        }
        None
    }

    pub fn count_fours(&self, pos: Pos, side: Side) -> u8 {
        self.count_fours_horizontal(pos, side)
    }

    fn count_fours_impl(&self, pos: Pos, our_row: u32, their_row: u32) -> u8 {
        debug_assert!(SIZE == BOARD_SIZE || SIZE == DIAG_SIZE);
        let mask_len = 7;

        // detect four by counting missing piece for a five (i.e. win with no overline)
        let max = (pos.col()).min(SIZE - mask_len);
        let min = pos.col().saturating_sub(mask_len - 1);

        let mut count = 0;
        let mut straight = false;

        for shift in min..=max {
            let win = 0b0111110 << shift;
            let win_mask = 0b1111111 << shift;
            let mask = 0b11111 << shift;

            let masked_row = our_row & win_mask;
            let missing = masked_row ^ win;

            // TODO: Check if this code actually properly works, and does not falsely report fours
            //can never be a four if there is an opposing piece in the 5 piece window
            if (their_row & mask) == 0 && missing.count_ones() == 1 {
                count += 1;

                //TODO might be faster by just checking all possible straight fours on masked_row
                if masked_row.wrapping_shr(masked_row.trailing_zeros()) == 0b01111 {
                    straight = true;
                }
            }
        }

        if straight && count > 1 {
            count -= 1
        }
        debug_assert!(!straight || count > 0);
        count
    }

    pub fn count_potential_fours(&self, pos: Pos, side: Side) -> u8 {
        debug_assert!(SIZE == BOARD_SIZE || SIZE == DIAG_SIZE);

        let our_row = set_bit(self.get_row(pos.row(), side), pos.col(), true);
        let their_row = self.get_row(pos.row(), !side);
        self.count_fours_impl(pos, our_row, their_row)
    }

    fn count_fours_horizontal(&self, pos: Pos, side: Side) -> u8 {
        debug_assert!(SIZE == BOARD_SIZE || SIZE == DIAG_SIZE);

        let our_row = self.get_row(pos.row(), side);
        let their_row = self.get_row(pos.row(), !side);
        self.count_fours_impl(pos, our_row, their_row)
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

    pub const fn normal_boundary_board() -> BitBoard<BOARD_SIZE> {
        let mut board: BitBoard<BOARD_SIZE> = BitBoard::filled();
        let mut row = 0;

        while row < BOARD_SIZE {
            let mut col = 0;
            while col < BOARD_SIZE {
                board = board.set_move(Pos::new(row, col), false);
                col += 1;
            }
            row += 1;
        }
        board
    }

    pub const fn diag_boundary_board() -> BitBoard<DIAG_SIZE> {
        let mut board: BitBoard<DIAG_SIZE> = BitBoard::new();
        let mut row = 0;

        while row < BOARD_SIZE {
            let mut col = 0;
            while col < BOARD_SIZE {
                let pos = Pos::new(row, col);
                board = board.set_move(Self::diag_right(pos), true);
                col += 1;
            }
            row += 1;
        }

        board.not()
    }

    pub fn at(&self, pos: Pos) -> Square {
        self.board0.at(pos)
    }

    pub const fn diag_right(pos: Pos) -> Pos {
        let pos = Self::rot_right(pos);
        let v = (DIAG_SIZE / 2).abs_diff(pos.row());
        let pos = Pos::new(pos.row(), pos.col() - v);
        let pos = Pos::new(pos.row(), pos.col() - (pos.col() / 2));
        pos
    }

    pub const fn diag_left(pos: Pos) -> Pos {
        let pos = Self::rot_left(pos);
        let v = (DIAG_SIZE / 2).abs_diff(pos.row());
        let pos = Pos::new(pos.row(), pos.col() - v);
        let pos = Pos::new(pos.row(), pos.col() - (pos.col() / 2));
        pos
    }

    pub const fn rot_right(pos: Pos) -> Pos {
        Self::rot_left(pos).transpose()
    }

    pub fn gen_table<F: Fn(Pos) -> Pos>(f: F) {
        let mut transformed = HashMap::new();
        let mut inverse = HashMap::new();

        let mut max_row = 0;
        let mut max_col = 0;

        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                let pos = Pos::new(row, col);

                let tpos = f(pos);

                max_row = max_row.max(tpos.row());
                max_col = max_col.max(tpos.col());

                transformed.insert(pos, tpos);
                inverse.insert(tpos, pos);
            }
        }
        print!("const TRANSFORM_TABLE: &'static [&'static [Pos]] = &[");

        for row in 0..BOARD_SIZE {
            print!("&[");
            for col in 0..BOARD_SIZE {
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

    //https://math.stackexchange.com/a/733222
    pub const fn rot_left(pos: Pos) -> Pos {
        Pos::new(
            pos.row() + pos.col(),
            (BOARD_SIZE - 1) - pos.row() + pos.col(),
        )
    }

    pub fn set(&mut self, pos: Pos, val: Square) {
        self.board0.set(pos, val);
        self.board1.set(pos.transpose(), val);
        self.board2.set(transform_right(pos), val);
        self.board3.set(transform_left(pos), val);
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
                assert_eq!(self.board2.at(Self::diag_right(pos)), val);
                assert_eq!(self.board3.at(Self::diag_left(pos)), val);
            }
        }
    }

    pub fn is_overline(&self, pos: Pos, side: Side) -> bool {
        self.board0.is_overline(pos, side)
            || self.board1.is_overline(pos, side)
            || self.board2.is_overline(pos, side)
            || self.board3.is_overline(pos, side)
    }

    pub fn is_win(&self, pos: Pos, side: Side) -> bool {
        self.board0.is_win(pos, side)
            || self.board1.is_win(pos, side)
            || self.board2.is_win(pos, side)
            || self.board3.is_win(pos, side)
    }

    pub fn is_double_three(&self, pos: Pos, side: Side) -> bool {
        self.count_threes(pos, side) >= 2
    }

    pub fn get_threes(&self, pos: Pos, side: Side) -> [Option<Pos>; 4] {
        [
            self.board0.get_three(pos, side),
            self.board1
                .get_three(pos.transpose(), side)
                .map(Pos::transpose),
            self.board2
                .get_three(transform_right(pos), side)
                .map(untransform_right),
            self.board3
                .get_three(transform_left(pos), side)
                .map(untransform_left),
        ]
    }

    // Renju double threes are a bit special, it is only a double three if it guarantees a win, so
    // take for example the following board:
    // h8g9g11e12h12i13e14
    //
    // One might think that e11 is a forbidden move for black, as it would result in two threes,
    // one where you create a straight four on e13 and one on f10. However, f10 would actually be a
    // double four, which is a forbidden move, so in reality we only have created one possible for
    // a straight four, and thus not a guaranteed win.
    //
    // See: https://www.renju.net/rifrules/ 9.3a
    pub fn is_renju_double_three(&self, pos: Pos, side: Side) -> bool {
        let cnt = self.get_threes(pos, side)
            .iter()
            .filter_map(|x| *x)
            .filter(|pos| self.count_potential_fours(*pos, side) >= 2)
            .count();
        cnt > 1
    }

    pub fn count_threes(&self, pos: Pos, side: Side) -> u8 {
        if self.board0.at(pos) != Square::Piece(side) {
            return 0;
        }

        let mut three_count = 0;

        if self.board0.get_three(pos, side) != None {
            three_count += 1;
        }
        if self.board1.get_three(pos.transpose(), side) != None {
            three_count += 1;
        }
        if self.board2.get_three(Self::diag_right(pos), side) != None {
            three_count += 1;
        }
        if self.board3.get_three(Self::diag_left(pos), side) != None {
            three_count += 1;
        }

        three_count
    }

    pub fn is_double_four(&self, pos: Pos, side: Side) -> bool {
        self.count_fours(pos, side) >= 2
    }

    pub fn count_fours(&self, pos: Pos, side: Side) -> u8 {
        let mut count = 0;

        count += self.board0.count_fours(pos, side);
        count += self.board1.count_fours(pos.transpose(), side);
        count += self.board2.count_fours(Self::diag_right(pos), side);
        count += self.board3.count_fours(Self::diag_left(pos), side);

        count
    }

    pub fn count_potential_fours(&self, pos: Pos, side: Side) -> u8 {
        let mut count = 0;

        count += self.board0.count_potential_fours(pos, side);
        count += self.board1.count_potential_fours(pos.transpose(), side);
        count += self
            .board2
            .count_potential_fours(Self::diag_right(pos), side);
        count += self
            .board3
            .count_potential_fours(Self::diag_left(pos), side);

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
    use super::{BitBoard, Board, PieceBoard, Pos, Side, Square, BOARD_SIZE, DIAGONAL_BOUNDARY};
    use crate::table::*;
    use anyhow::Result;

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

        assert_eq!(board.count_threes("f10".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("g9".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("h8".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn incorrect_three() -> Result<()> {
        let board: Board = "h4h5h6h8".parse()?;

        assert_eq!(board.count_threes("h8".parse()?, Side::Black), 0);
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
    fn no_double_four() -> Result<()> {
        let board: Board = "g8h8i8j8".parse()?;

        assert_eq!(board.count_fours("j8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("g8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("h8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("i8".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn no_diag_three_at_edge() -> Result<()> {
        let board: Board = "i1h2f4".parse()?;

        assert_eq!(board.count_threes("i1".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("h2".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("f4".parse()?, Side::Black), 0);
        Ok(())
    }

    #[test]
    fn vertical_straight_four() -> Result<()> {
        let board: Board = "h8h9h10h11".parse()?;

        assert_eq!(board.count_fours("h8".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn win_no_four() -> Result<()> {
        let board: Board = "h8h9h10h11h12".parse()?;

        assert_eq!(board.count_fours("h6".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h7".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h8".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h9".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h10".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h11".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h12".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h13".parse()?, Side::Black), 0);
        assert_eq!(board.count_fours("h14".parse()?, Side::Black), 0);
        Ok(())
    }

    #[test]
    fn diag_straight_four() -> Result<()> {
        let board: Board = "g7h8i9j10".parse()?;

        assert_eq!(board.count_fours("g7".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("h8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("i9".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("j10".parse()?, Side::Black), 1);
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
    fn overline_is_not_three() -> Result<()> {
        let board: Board = "e8f8h8j8".parse()?;

        assert_eq!(board.count_threes("e8".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("f8".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("h8".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("j8".parse()?, Side::Black), 0);

        Ok(())
    }

    #[test]
    fn three_near_edge_horiz() -> Result<()> {
        let board: Board = "b14c14d14".parse()?;

        assert_eq!(board.count_threes("b14".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("c14".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("d14".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn three_near_edge_diag() -> Result<()> {
        let board: Board = "d12c13b14".parse()?;

        assert_eq!(board.count_threes("d12".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("c13".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("b14".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn three_near_edge_diag2() -> Result<()> {
        let board: Board = "d5c6b7".parse()?;

        println!("{:?}", DIAGONAL_BOUNDARY);
        assert_eq!(board.count_threes("d5".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("c6".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("b7".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn four_near_edge_horiz() -> Result<()> {
        let board: Board = "b8c8d8e8".parse()?;

        assert_eq!(board.count_fours("b8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("c8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("d8".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("e8".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn four_near_edge_diag() -> Result<()> {
        let board: Board = "f11e12d13c14".parse()?;

        assert_eq!(board.count_fours("f11".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("e12".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("d13".parse()?, Side::Black), 1);
        assert_eq!(board.count_fours("c14".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn double_three_near_edge() -> Result<()> {
        let board: Board = "f12e13b14c14d14".parse()?;

        assert_eq!(board.is_double_three("d14".parse()?, Side::Black), true);
        Ok(())
    }

    #[test]
    fn no_double_three_single_diag() -> Result<()> {
        let board: Board = "f7h9i10k12".parse()?;

        assert_eq!(board.count_threes("f7".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("h9".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("i10".parse()?, Side::Black), 0);
        assert_eq!(board.count_threes("k12".parse()?, Side::Black), 0);
        Ok(())
    }

    #[test]
    fn diag_three_no_overline() -> Result<()> {
        let board: Board = "e5h8i9j10".parse()?;

        assert_eq!(board.count_threes("h8".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("i9".parse()?, Side::Black), 1);
        assert_eq!(board.count_threes("j10".parse()?, Side::Black), 1);
        Ok(())
    }

    #[test]
    fn get_threes() -> Result<()> {
        let board: Board = "h8g9e11g11e12h12i13e14".parse()?;

        let [a, b, c, d] = board.get_threes("e11".parse()?, Side::Black);

        assert_eq!(a, None);
        assert_eq!(b, Some("e13".parse()?));
        assert_eq!(c, None);
        assert_eq!(d, Some("f10".parse()?));
        Ok(())
    }

    #[test]
    fn is_renju_double_three() -> Result<()> {
        let board: Board = "h8g9e11g11e12h12i13e14".parse()?;

        assert_eq!(board.is_renju_double_three("e11".parse()?, Side::Black), false);
        Ok(())
    }

    #[test]
    fn test_transforms() {
        for row in 0..BOARD_SIZE {
            for col in 0..BOARD_SIZE {
                let pos = Pos::new(row, col);

                assert_eq!(Board::diag_right(pos), transform_right(pos));
                assert_eq!(Board::diag_left(pos), transform_left(pos));

                assert_eq!(untransform_right(transform_right(pos)), pos);
                assert_eq!(untransform_left(transform_left(pos)), pos);
            }
        }
    }

    #[test]
    fn potential_fours() -> Result<()> {
        let board: Board = "h8g9e11g11e12h12i13e14".parse()?;

        assert_eq!(board.count_potential_fours("f10".parse()?, Side::Black), 2);
        Ok(())
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
