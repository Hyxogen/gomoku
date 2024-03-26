mod board;

use board::{Board, Side};
use protocol::{BrainCommand, Field, ManagerCommand, ManagerCommandReader};
use std::borrow::Cow;
use std::io;
use std::io::Write;
use tools::Pos;

pub struct BrainClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    ostream: W,
    istream: ManagerCommandReader<'a, R>,
}

impl<'a, R, W> BrainClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    pub fn new(istream: R, ostream: W) -> Self {
        Self {
            istream: ManagerCommandReader::new(istream),
            ostream,
        }
    }

    pub fn error(&mut self, s: &str) {
        writeln!(self.ostream, "ERROR: {}", s).unwrap();
    }

    pub fn ack(&mut self) {
        writeln!(self.ostream, "OK").unwrap();
    }

    pub fn send(&mut self, cmd: BrainCommand) {
        writeln!(self.ostream, "{}", cmd).unwrap();
    }
}

impl<'a, R, W> Iterator for BrainClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    type Item = ManagerCommand<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cmd) = self.istream.next() {
            match cmd {
                Ok(cmd) => return Some(cmd),
                Err(err) => self.error(&format!("invalid command: {}", err)),
            }
        }
        None
    }
}

fn is_forbidden(pos: Pos, board: &mut Board) -> bool {
    /*if board.at(pos) != Square::Empty {
        return false;
    }

    board.set(pos, Square::Piece(Side::Black));

    let forbidden = board.is_overline(pos, Side::Black)
        || (!board.is_win(pos, Side::Black)
            && (board.is_renju_double_three(pos, Side::Black) || board.is_double_four(pos, Side::Black)));
    board.set(pos, Square::Empty);
    forbidden*/
    false
}

pub fn main() {
    //let reader = ManagerCommandReader::new(io::stdin().lines().map(|line| line.unwrap()));
    let mut client = BrainClient::new(io::stdin().lines().map(|line| line.unwrap()), io::stdout());

    let mut initialized = false;
    let mut board = Board::new();

    while let Some(cmd) = client.next() {
        match cmd {
            ManagerCommand::Start(size) if size == 15 => {
                board = Board::new();
                initialized = true;
                client.ack();
            }
            ManagerCommand::Start(_) => {
                client.error("unsupported board size");
            }
            ManagerCommand::YXBoard(pieces) if initialized => {
                board = Board::new();
                for (pos, field) in pieces.as_ref() {
                    let side = match field {
                        Field::Mine => Side::Black,
                        Field::Theirs => Side::White,
                    };

                    board.set(*pos, Some(side));
                }
            }
            ManagerCommand::YXShowForbid if initialized => {
                let mut forbidden = Vec::new();
                for row in 0..15 {
                    for col in 0..15 {
                        let pos = Pos::new(row, col);
                        if is_forbidden(pos, &mut board) {
                            forbidden.push(pos);
                        }
                    }
                }

                client.send(BrainCommand::Forbid(Cow::Owned(forbidden)));
            }
            ManagerCommand::Info(_, _) if initialized => {}
            _ if !initialized => {
                client.error("no game has been started");
            }
            _ => todo!(),
        }
    }
}
