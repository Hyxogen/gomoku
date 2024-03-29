use clap::Parser;
use macroquad::prelude::*;

use narabe::board::{Board, Side};
use tools::Pos;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = "")]
    board: String,
}

const LINE_WIDTH: f32 = 1.;

#[macroquad::main("gomoku")]
async fn main() {
    let args = Args::parse();
    let mut board: Board = args.board.parse().unwrap();
    let mut forbidden = board.renju_forbidden();
    let mut win = board.win();
    let mut overline = board.overline();
    let mut double_fours = board.double_fours();
    let mut threes = board.threes();

    let dots: &[Pos] = &[
        "h8".parse().unwrap(),
        "d12".parse().unwrap(),
        "d4".parse().unwrap(),
        "l12".parse().unwrap(),
        "l4".parse().unwrap(),
    ];

    loop {
        clear_background(YELLOW);

        let size = board.size();
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

            let row = (size as u8 - 1) - squarey as u8;
            let col = squarex as u8;
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

        for (pos, square) in board.squares() {
            let (x, y) = to_screen_coords(pos);

            if let Some(side) =  square {
                let color = if side == Side::Black { BLACK } else { WHITE };

                let r = square_width.min(square_height) / 2.;

                draw_circle(x, y, r, color);
            }
        }


        for row in 0..size {
            for col in 0..size {
                let pos = (row, col).into();
                let (x, y) = to_screen_coords(pos);

                if threes.at(pos) {
                    //draw_circle(x, y, 5., WHITE);
                }

                if win.at(pos) {
                    draw_circle(x, y, 5., GOLD);
                } else {
                    if forbidden.at(pos) {
                        draw_circle(x, y, 5., RED);
                    }

                    if overline.at(pos) {
                        draw_circle(x, y, 5., PURPLE);
                    }

                    if double_fours.at(pos) {
                        draw_circle(x, y, 5., BLUE);
                    }

                }
            }
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
            board = board.set(square, Some(side));
            forbidden = board.renju_forbidden();
            win = board.win();
            overline = board.overline();
            double_fours = board.double_fours();
            threes = board.threes();
        }
        if is_mouse_button_down(MouseButton::Middle) {
            board = board.set(square, None);
            forbidden = board.renju_forbidden();
            win = board.win();
            overline = board.overline();
            double_fours = board.double_fours();
            threes = board.threes();
        }

        if is_key_down(KeyCode::C) {
            println!("{}", board);
        }

        if is_key_down(KeyCode::R) {
            board = Board::new();
        }

        if is_key_down(KeyCode::D) {
            eprintln!("{:?}", board);
        }

        if is_key_down(KeyCode::Escape) || is_key_down(KeyCode::Q) {
            break;
        }

        next_frame().await
    }
}
