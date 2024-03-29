use clap::Parser;
use narabe::board::{BitBoard, Board, Side, RENJU_BOARD_SIZE, RENJU_BOARD_SIZEU8};
use protocol::{BrainCommand, BrainCommandReader, Field, ManagerCommand};
use rand::random;
use std::borrow::Cow;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};
use tools::Pos;

#[derive(Parser, Debug)]
struct Args {
    bot: PathBuf,

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

    pub fn send(&mut self, cmd: ManagerCommand) {
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

fn board_to_field(board: &Board) -> impl Iterator<Item = (Pos, Field)> + '_ {
    board.pieces().map(|(pos, side)| {
        let field = if side == Side::Black {
            Field::Mine
        } else {
            Field::Theirs
        };

        (pos, field)
    })
}

fn get_forbids<'a, R, W>(
    board: &Board,
    bot: &mut ManagerClient<'a, R, W>,
) -> BitBoard<RENJU_BOARD_SIZE>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    bot.send(ManagerCommand::YXBoard(Cow::Owned(
        board_to_field(board).collect(),
    )));
    bot.send(ManagerCommand::YXShowForbid);

    let resp = bot.next().unwrap();
    if let BrainCommand::Forbid(forbidden) = resp {
        let mut board = BitBoard::new();

        for pos in forbidden.into_owned() {
            board = board.set(pos, true);
        }
        board
    } else {
        panic!("invalid reponse")
    }
}

fn test_field<'a, R, W>(
    board: &Board,
    bot: &mut ManagerClient<'a, R, W>,
) -> Option<(BitBoard<RENJU_BOARD_SIZE>, BitBoard<RENJU_BOARD_SIZE>)>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    let expected = get_forbids(board, bot);
    let actual = board.renju_forbidden();

    if expected == actual {
        None
    } else {
        Some((actual, expected))
    }
}

fn reduce_aggresive<'a, R, W>(
    board: &Board,
    bot: &mut ManagerClient<'a, R, W>,
) -> (
    Board,
    BitBoard<RENJU_BOARD_SIZE>,
    BitBoard<RENJU_BOARD_SIZE>,
)
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    let mut res = Default::default();
    let mut reduced = *board;
    'outer: loop {
        for skip in 0..reduced.pieces().count() {
            let attempt = reduced.set(reduced.pieces().nth(skip).unwrap().0, None);

            if let Some(diff) = test_field(&attempt, bot) {
                reduced = attempt;
                res = diff;
                continue 'outer;
            }
        }
        break;
    }
    (reduced, res.0, res.1)
}

fn test_and_reduce<'a, R, W>(
    board: &Board,
    bot: &mut ManagerClient<'a, R, W>,
) -> Result<
    (),
    (
        Board,
        BitBoard<RENJU_BOARD_SIZE>,
        BitBoard<RENJU_BOARD_SIZE>,
    ),
>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    if test_field(board, bot) != None {
        Err(reduce_aggresive(board, bot))
    } else {
        Ok(())
    }
}

fn test<'a, R, W>(board: &Board, bot: &mut ManagerClient<'a, R, W>) -> bool
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    match test_and_reduce(board, bot) {
        Ok(_) => {
            println!("OK");
            true
        }
        Err((reduced, ours, theirs)) => {
            let mut stdout = StandardStream::stdout(ColorChoice::Always);

            writeln!(stdout, "KO").unwrap();
            writeln!(stdout, "board: {}", board).unwrap();
            writeln!(stdout, "reduced: {}", reduced).unwrap();
            for row in 0..RENJU_BOARD_SIZEU8 {
                for col in 0..RENJU_BOARD_SIZEU8 {
                    let pos = (row, col).into();

                    let ours = ours.at(pos);
                    let theirs = theirs.at(pos);

                    if !ours && !theirs {
                        continue;
                    }

                    if ours && !theirs {
                        stdout
                            .set_color(ColorSpec::new().set_fg(Some(Color::Red)))
                            .unwrap();
                    } else if !ours && theirs {
                        stdout
                            .set_color(ColorSpec::new().set_fg(Some(Color::Green)))
                            .unwrap();
                    } else {
                        stdout.set_color(ColorSpec::new().set_reset(true)).unwrap();
                    }

                    write!(stdout, "{} ", pos).unwrap();
                }
            }
            stdout.set_color(ColorSpec::new().set_reset(true)).unwrap();
            writeln!(stdout).unwrap();
            false
        }
    }
}

fn random_pos(max: u8) -> Pos {
    Pos::new(random::<u8>() % max, random::<u8>() % max)
}

fn random_board(max_pieces: u16) -> Board {
    let mut board = Board::new();
    let npieces: u16 = random::<u16>() % max_pieces;

    for _ in 0..npieces {
        board = board.set(random_pos(board.size()), Some(Side::Black));
    }
    board
}

fn main() {
    let args = Args::parse();

    let bot = Command::new(args.bot)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let mut client = ManagerClient::new(
        BufReader::new(bot.stdout.unwrap())
            .lines()
            .map(|line| line.unwrap()),
        bot.stdin.unwrap(),
    );

    client.send(ManagerCommand::Start(15));
    client.send(ManagerCommand::Info("rule".to_string(), "4".to_string()));

    if let Some(board) = args.board {
        let board = board.parse().unwrap();

        test(&board, &mut client);
    } else {
        loop {
            let board = random_board(15 * 15);

            if !test(&board, &mut client) {
                break;
            }
        }
    }
}
