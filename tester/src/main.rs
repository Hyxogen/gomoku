use clap::Parser;
use narabe::board::{Board, Side, Square};
use protocol::{BrainCommand, BrainCommandReader, Field, ManagerCommand};
use rand::random;
use std::borrow::Cow;
use std::collections::BTreeSet;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};
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

fn get_forbids<'a, R1, W1, R2, W2>(
    pos: &Vec<(Pos, Field)>,
    bot1: &mut ManagerClient<'a, R1, W1>,
    bot2: &mut ManagerClient<'a, R2, W2>,
) -> (BTreeSet<Pos>, BTreeSet<Pos>)
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

    let resp1 = bot1.next();
    let resp2 = bot2.next().unwrap();
    match (resp1, resp2) {
        (Some(BrainCommand::Forbid(pos1)), BrainCommand::Forbid(pos2)) => (
            pos1.into_owned().into_iter().collect(),
            pos2.into_owned().into_iter().collect(),
        ),
        (_, BrainCommand::Forbid(pos2)) => {
            (Default::default(), pos2.into_owned().into_iter().collect())
        }
        _ => panic!("invalid response"),
    }
}

fn reduce<'a, R1, W1, R2, W2>(
    pos: &Vec<(Pos, Field)>,
    org: (&BTreeSet<Pos>, &BTreeSet<Pos>),
    bot1: &mut ManagerClient<'a, R1, W1>,
    bot2: &mut ManagerClient<'a, R2, W2>,
) -> Vec<(Pos, Field)>
where
    R1: Iterator,
    R1::Item: AsRef<str>,
    W1: Write,
    R2: Iterator,
    R2::Item: AsRef<str>,
    W2: Write,
{
    let mut reduced = pos.clone();
    'outer: loop {
        for skip in 0..reduced.len() {
            let attempt = reduced
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != skip)
                .map(|(_, v)| *v)
                .collect();

            let new = get_forbids(&attempt, bot1, bot2);

            if new.0.difference(org.0).count() == 0 && new.1.difference(org.1).count() == 0 {
                reduced = attempt;
                continue 'outer;
            }
        }
        break;
    }
    reduced
}

fn reduce_aggresive<'a, R1, W1, R2, W2>(
    pos: &Vec<(Pos, Field)>,
    bot1: &mut ManagerClient<'a, R1, W1>,
    bot2: &mut ManagerClient<'a, R2, W2>,
) -> Vec<(Pos, Field)>
where
    R1: Iterator,
    R1::Item: AsRef<str>,
    W1: Write,
    R2: Iterator,
    R2::Item: AsRef<str>,
    W2: Write,
{
    let mut reduced = pos.clone();
    'outer: loop {
        for skip in 0..reduced.len() {
            let attempt = reduced
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != skip)
                .map(|(_, v)| *v)
                .collect();

            let (resp1, resp2) = get_forbids(&attempt, bot1, bot2);

            if resp1.difference(&resp2).count() != 0 {
                reduced = attempt;
                continue 'outer;
            }
        }
        break;
    }
    reduced
}

fn pos_to_board(positions: &Vec<(Pos, Field)>) -> Board {
    let mut board = Board::new();

    for (pos, field) in positions {
        let side = if let Field::Mine = field {
            Side::Black
        } else {
            Side::White
        };
        board.set(*pos, Square::Piece(side));
    }
    board
}

fn print_differences(resp1: &BTreeSet<Pos>, resp2: &BTreeSet<Pos>) {
    let mut stdout = StandardStream::stdout(ColorChoice::Always);
    writeln!(stdout, "BOT 1:").unwrap();
    for pos in resp1 {
        if !resp2.contains(pos) {
            stdout
                .set_color(ColorSpec::new().set_fg(Some(Color::Red)))
                .unwrap();
        } else {
            stdout
                .set_color(ColorSpec::new().set_fg(Some(Color::Green)))
                .unwrap();
        }

        writeln!(stdout, "{} row={} col={}", pos, pos.row(), pos.col()).unwrap();
    }
    stdout.set_color(ColorSpec::new().set_reset(true)).unwrap();
    if resp1.is_empty() {
        writeln!(stdout, "NONE").unwrap();
    }

    writeln!(stdout, "BOT 2:").unwrap();

    for pos in resp2 {
        if !resp2.contains(pos) {
            stdout
                .set_color(ColorSpec::new().set_fg(Some(Color::Red)))
                .unwrap();
        } else {
            stdout
                .set_color(ColorSpec::new().set_fg(Some(Color::Green)))
                .unwrap();
        }

        writeln!(stdout, "{} row={} col={}", pos, pos.row(), pos.col()).unwrap();
    }

    stdout.set_color(ColorSpec::new().set_reset(true)).unwrap();
    if resp2.is_empty() {
        writeln!(stdout, "NONE").unwrap();
    }
    writeln!(stdout).unwrap();
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
    let (resp1, resp2) = get_forbids(positions, bot1, bot2);
    if resp1.difference(&resp2).count() != 0 {
        print_differences(&resp1, &resp2);

        let board = pos_to_board(positions);
        eprintln!("board: {}", board);

        let reduced = reduce(positions, (&resp1, &resp2), bot1, bot2);
        let areduced = reduce_aggresive(positions, bot1, bot2);
        eprintln!("reduced board: {}", pos_to_board(&reduced));

        eprintln!();
        eprintln!("AGGRESSIVE REDUCTION:");
        eprintln!("reduced board: {}", pos_to_board(&areduced));

        let (resp1, resp2) = get_forbids(&areduced, bot1, bot2);
        print_differences(&resp1, &resp2);
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
