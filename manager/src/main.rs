use clap::Parser;
use macroquad::prelude::*;

use narabe::board::{Board, Side, Square};
use protocol::{BrainCommand, BrainCommandReader, Field, ManagerCommand};
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::{Command, Stdio};
use tools::Pos;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = "")]
    board: String,

    bot: PathBuf,
}

const LINE_WIDTH: f32 = 1.;

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
        write!(self.ostream, "{}", cmd).unwrap();
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
                Ok(cmd) => return Some(cmd),
                Err(_) => todo!(),
            }
        }
        None
    }
}

fn read_positions(board: &Board, side: Side) -> Vec<(Pos, Field)> {
    let mut vec = Vec::new();

    for row in 0..15 {
        for col in 0..15 {
            let pos = Pos::new(row, col);
            if let Square::Piece(s) = board.at(pos) {
                let field = if s == side {
                    Field::Mine
                } else {
                    Field::Theirs
                };
                vec.push((pos, field));
            }
        }
    }
    vec
}

#[macroquad::main("gomoku")]
async fn main() {
    let args = Args::parse();
    let mut board: Board = args.board.parse().unwrap();

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

    client.send(&ManagerCommand::Start(15));

    let dots: &[Pos] = &[
        "h8".parse().unwrap(),
        "d12".parse().unwrap(),
        "d4".parse().unwrap(),
        "l12".parse().unwrap(),
        "l4".parse().unwrap(),
    ];

    let mut forbidden: Vec<Pos> = Vec::new();

    loop {
        clear_background(YELLOW);

        let size = board.size() as u8;
        let square_width = screen_width() / size as f32;
        let square_height = screen_height() / size as f32;
        let width = screen_width() - square_width;
        let height = screen_height() - square_height;

        let xoff = square_width / 2.0;
        let yoff = square_height / 2.0;

        let to_screen_coords = |pos: Pos| -> (f32, f32) {
            (
                pos.col() as f32 * square_width + xoff,
                (size - 1 - pos.row() as u8) as f32 * square_height + yoff,
            )
        };

        let from_screen_coords = |pos: (f32, f32)| -> Pos {
            let squarex = ((pos.0 - xoff) / square_width).round();
            let squarey = ((pos.1 - yoff) / square_height).round();

            let row = (size as usize - 1) - squarey as usize;
            let col = squarex as usize;
            (row, col).into()
        };

        for i in 0..size {
            let y = i as f32 * square_height;
            draw_line(xoff, y + yoff, width + xoff, y + yoff, LINE_WIDTH, BLACK);
            draw_text(&(size - i).to_string(), 0.0, y + yoff, 20.0, BLACK);

            let x = i as f32 * square_width;
            draw_line(x + xoff, yoff, x + xoff, height + yoff, LINE_WIDTH, BLACK);
            draw_text(
                &(('A' as u8 + i) as char).to_string(),
                x + xoff,
                yoff - 1.,
                20.0,
                BLACK,
            );
        }

        for row in 0..size {
            for col in 0..size {
                let pos = (row, col).into();
                let (x, y) = to_screen_coords(pos);

                if let Square::Piece(side) = board.at(pos) {
                    let color = if side == Side::Black { BLACK } else { WHITE };

                    let r = square_width.min(square_height) / 2.;

                    draw_circle(x, y, r, color);
                } else {
                    board.set(pos, Square::Piece(Side::Black));

                    if board.is_overline(pos, Side::Black)
                        || (!board.is_win(pos, Side::Black)
                            && (board.is_double_three(pos, Side::Black)
                                || board.is_double_four(pos, Side::Black)))
                    {
                        draw_circle(x, y, 5., RED);
                    }

                    if board.is_win(pos, Side::Black) && !board.is_overline(pos, Side::Black) {
                        draw_circle(x, y, 5., GOLD);
                    }

                    board.set(pos, Square::Empty);
                }

                if board.count_threes(pos, Side::Black) > 0 {
                    draw_circle(x, y, 5., GREEN);
                }

                if board.count_fours(pos, Side::Black) > 0 {
                    draw_circle(x, y, 5., PURPLE);
                }

                if board.is_overline(pos, Side::Black) {
                    draw_circle(x, y, 5., DARKPURPLE);
                }
            }
        }

        for pos in forbidden.iter() {
            let (x, y) = to_screen_coords(*pos);
            draw_circle(x, y, 7., RED);
        }

        for dot in dots {
            let (x, y) = to_screen_coords(*dot);
            draw_circle(x, y, 3., BLACK);
        }

        let mouse_pos = mouse_position();
        let square = from_screen_coords(mouse_pos);

        let (x, y) = to_screen_coords(square);
        draw_circle(x, y, 10., BLUE);

        if is_mouse_button_down(MouseButton::Left) {
            let side = if is_key_down(KeyCode::LeftShift) {
                Side::White
            } else {
                Side::Black
            };
            board.set(square, Square::Piece(side));

            client.send(&ManagerCommand::YXBoard(read_positions(
                &board,
                Side::Black,
            )));
        }
        if is_mouse_button_down(MouseButton::Middle) {
            board.set(square, Square::Empty);
            client.send(&ManagerCommand::YXBoard(read_positions(
                &board,
                Side::Black,
            )));
        }

        if is_key_down(KeyCode::C) {
            println!("{}", board);
        }

        if is_key_down(KeyCode::R) {
            board = Board::new();
        }

        if is_key_down(KeyCode::F) {
            client.send(&ManagerCommand::YXShowForbid);

            if let Some(BrainCommand::Forbid(positions)) = client.next()  {
                forbidden = positions.into_owned();
            } else {
                panic!("expected forbidden positions");
            }
        }

        next_frame().await
    }
}
