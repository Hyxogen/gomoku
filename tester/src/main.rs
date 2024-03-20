use clap::Parser;
use narabe::board::{Board, Side, Square};
use protocol::{BrainCommand, BrainCommandReader, Field, ManagerCommand};
use rand::random;
use std::borrow::Cow;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use tools::Pos;

#[derive(Parser, Debug)]
struct Args {
    bot1: PathBuf,
    bot2: PathBuf,

    board: Option<String>,
}

pub struct ManagerClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    ostream: W,
    istream: BrainCommandReader<'a, R>,
}

impl<'a, R, W> ManagerClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    pub fn new(istream: R, ostream: W) -> Self {
        Self {
            istream: BrainCommandReader::new(istream),
            ostream,
        }
    }

    pub fn send(&mut self, cmd: &ManagerCommand) {
        writeln!(self.ostream, "{}", cmd).unwrap();
    }
}

impl<'a, R, W> Iterator for ManagerClient<'a, R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    type Item = BrainCommand<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cmd) = self.istream.next() {
            match cmd {
                Ok(BrainCommand::Ack) => (),
                Ok(BrainCommand::Debug(_)) | Ok(BrainCommand::Message(_)) => (),
                Ok(cmd) => return Some(cmd),
                Err(err) => eprintln!("parse error: {}", err),
            }
        }
        None
    }
}

//e3d4f4i5j5a6c6f7b9c12b14g14
fn test_board<'a, R1, W1, R2, W2>(
    pos: &Vec<(Pos, Field)>,
    bot1: &mut ManagerClient<'a, R1, W1>,
    bot2: &mut ManagerClient<'a, R2, W2>,
) -> bool
where
    R1: Iterator,
    R1::Item: AsRef<str>,
    W1: Write,
    R2: Iterator,
    R2::Item: AsRef<str>,
    W2: Write,
{
    bot1.send(&ManagerCommand::YXBoard(Cow::Borrowed(pos)));
    bot1.send(&ManagerCommand::YXShowForbid);
    bot2.send(&ManagerCommand::YXBoard(Cow::Borrowed(pos)));
    bot2.send(&ManagerCommand::YXShowForbid);

    let resp1 = bot1.next().unwrap();
    let resp2 = bot2.next().unwrap();

    match (resp1, resp2) {
        (BrainCommand::Forbid(pos1), BrainCommand::Forbid(pos2)) => {
            let mut pos1 = pos1.into_owned();
            let mut pos2 = pos2.into_owned();

            pos1.sort();
            pos2.sort();

            if pos1 != pos2 {
                eprintln!("different forbidden positions!");

                eprintln!("bot1:");
                for pos in pos1 {
                    eprintln!("{} row={} col={}", pos, pos.row(), pos.col());
                }

                eprintln!("bot2:");
                for pos in pos2 {
                    eprintln!("{} row={} col={}", pos, pos.row(), pos.col());
                }
                false
            } else {
                true
            }
        }
        _ => panic!("invalid response"),
    }
}

fn test_single<'a, R1, W1, R2, W2>(
    positions: &Vec<(Pos, Field)>,
    bot1: &mut ManagerClient<'a, R1, W1>,
    bot2: &mut ManagerClient<'a, R2, W2>,
) where
    R1: Iterator,
    R1::Item: AsRef<str>,
    W1: Write,
    R2: Iterator,
    R2::Item: AsRef<str>,
    W2: Write,
{
    if !test_board(positions, bot1, bot2) {
        let mut board = Board::new();
        eprintln!("field:");

        for (pos, field) in positions {
            let side = if let Field::Mine = field {
                Side::Black
            } else {
                Side::White
            };
            board.set(*pos, Square::Piece(side));

            let field = if let Field::Mine = field { 1 } else { 2 };
            eprintln!("{},{},{}", pos.col(), pos.row(), field);
        }

        eprintln!("board: {}", board);
        std::process::exit(1);
    } else {
        println!("OK");
    }
}

fn main() {
    let args = Args::parse();

    let bot1 = Command::new(args.bot1)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let mut client1 = ManagerClient::new(
        BufReader::new(bot1.stdout.unwrap())
            .lines()
            .map(|line| line.unwrap()),
        bot1.stdin.unwrap(),
    );

    let bot2 = Command::new(args.bot2)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let mut client2 = ManagerClient::new(
        BufReader::new(bot2.stdout.unwrap())
            .lines()
            .map(|line| line.unwrap()),
        bot2.stdin.unwrap(),
    );

    client1.send(&ManagerCommand::Start(15));
    client2.send(&ManagerCommand::Start(15));
    client1.send(&ManagerCommand::Info("rule".to_string(), "4".to_string()));
    client2.send(&ManagerCommand::Info("rule".to_string(), "4".to_string()));

    if let Some(board) = args.board {
        let board: Board = board.parse().unwrap();

        let mut positions: Vec<(Pos, Field)> = Vec::new();

        for row in 0..board.size() {
            for col in 0..board.size() {
                let pos = Pos::new(row, col);

                match board.at(pos) {
                    Square::Piece(Side::Black) => positions.push((pos, Field::Mine)),
                    Square::Piece(Side::White) => positions.push((pos, Field::Theirs)),
                    _ => (),
                };
            }
        }

        test_single(&positions, &mut client1, &mut client2);
    } else {
        loop {
            let mut positions: Vec<(Pos, Field)> = Vec::new();

            let count = random::<u8>() % (15 * 15);

            for _ in 0..count {
                //let b: bool = random();
                //let field = if b { Field::Mine } else { Field::Theirs };

                let pos = (random::<u8>() % 15, random::<u8>() % 15).into();
                positions.push((pos, Field::Mine));
            }

            test_single(&positions, &mut client1, &mut client2);
        }
    }
}
