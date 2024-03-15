use nom::bytes::complete::tag_no_case;
use nom::character::streaming;
use nom::sequence::{delimited, Tuple};
use nom::IResult;
use tools::Pos;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Field {
    Mine,
    Theirs,
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ManagerCommand {
    Start(usize),
    Turn(Pos),
    Begin,
    Board(Vec<(Pos, Field)>),
    YXBoard(Vec<(Pos, Field)>),
    Info(String, String),
    End,
    About,
}

impl std::fmt::Display for ManagerCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Start(size) => writeln!(f, "START {}", size),
            Self::Turn(pos) => writeln!(f, "TURN {},{}", pos.col(), pos.row()),
            Self::Begin => writeln!(f, "BEGIN"),
            Self::Board(pieces) | Self::YXBoard(pieces) => {
                for (pos, field) in pieces {
                    writeln!(
                        f,
                        "{},{},{}",
                        pos.col(),
                        pos.row(),
                        if *field == Field::Mine { 1 } else { 2 }
                    )?;
                }
                writeln!(f, "DONE")
            }
            Self::Info(key, val) => writeln!(f, "INFO {} {}", key, val),
            Self::End => writeln!(f, "END"),
            Self::About => writeln!(f, "ABOUT"),
        }
    }
}

impl ManagerCommand {
    fn comma(s: &str) -> IResult<&str, char> {
        delimited(streaming::space0, streaming::one_of(","), streaming::space0)(s)
    }

    fn pos(s: &str) -> IResult<&str, Pos> {
        let (rem, (row, _, col)) = (streaming::u8, Self::comma, streaming::u8).parse(s)?;
        Ok((rem, (col, row).into()))
    }

    fn start(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, (_, _, size)) =
            (tag_no_case("start"), streaming::space1, streaming::u8).parse(s)?;
        Ok((rem, ManagerCommand::Start(size.into())))
    }

    fn turn(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, (_, _, pos)) = (tag_no_case("turn"), streaming::space1, Self::pos).parse(s)?;
        Ok((rem, ManagerCommand::Turn(pos)))
    }

    fn begin(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, _) = tag_no_case("begin")(s)?;
        Ok((rem, ManagerCommand::Begin))
    }

    fn field(s: &str) -> IResult<&str, Field> {
        let (rem, ch) = streaming::one_of("12")(s)?;

        let field = if ch == '1' {
            Field::Mine
        } else {
            Field::Theirs
        };

        Ok((rem, field))
    }

    fn board_piece(s: &str) -> IResult<&str, (Pos, Field)> {
        let (rem, (pos, _, field, _)) =
            (Self::pos, Self::comma, Self::field, streaming::multispace1).parse(s)?;
        Ok((rem, (pos, field)))
    }

    fn space0_line_ending(s: &str) -> IResult<&str, ()> {
        let (rem, _) = (streaming::space0, streaming::line_ending).parse(s)?;
        Ok((rem, ()))
    }

    fn done(s: &str) -> IResult<&str, ()> {
        let (rem, _) = (tag_no_case("done"),).parse(s)?;
        Ok((rem, ()))
    }

    fn board_pieces(s: &str) -> IResult<&str, Vec<(Pos, Field)>> {
        let (rem, (pieces, _)) = nom::multi::many_till(Self::board_piece, Self::done)(s)?;
        Ok((rem, pieces))
    }

    fn board(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, (_, _, pieces)) = (
            tag_no_case("board"),
            Self::space0_line_ending,
            Self::board_pieces,
        )
            .parse(s)?;
        Ok((rem, ManagerCommand::Board(pieces)))
    }

    fn yxboard(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, (_, _, pieces)) = (
            tag_no_case("yxboard"),
            Self::space0_line_ending,
            Self::board_pieces,
        )
            .parse(s)?;
        Ok((rem, ManagerCommand::YXBoard(pieces)))
    }

    fn command(s: &str) -> IResult<&str, ManagerCommand> {
        nom::branch::alt((
            Self::start,
            Self::begin,
            Self::turn,
            Self::board,
            Self::yxboard,
        ))(s)
    }

    fn parse(s: &str) -> IResult<&str, ManagerCommand> {
        let (rem, (_, command, _)) =
            (streaming::space0, Self::command, Self::space0_line_ending).parse(s)?;
        Ok((rem, command))
    }
}

#[derive(Debug)]
pub struct ParseError {
    inner: nom::error::Error<String>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl ParseError {
    fn new(inner: nom::error::Error<String>) -> Self {
        Self { inner }
    }
}

pub struct ManagerCommandReader<I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    inner: I,
}

impl<I> ManagerCommandReader<I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    pub fn new(inner: I) -> Self {
        Self { inner }
    }
}

impl<I> Iterator for ManagerCommandReader<I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    type Item = Result<ManagerCommand, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut cmd = String::new();

        loop {
            if let Some(line) = self.inner.next() {
                let line = line.as_ref().trim();
                cmd.push_str(line);
                cmd.push('\n');

                match ManagerCommand::parse(&cmd) {
                    Ok((_, cmd)) => return Some(Ok(cmd)),
                    Err(nom::Err::Incomplete(_)) => continue,
                    Err(err) => match err.to_owned() {
                        nom::Err::Error(err) | nom::Err::Failure(err) => {
                            return Some(Err(ParseError::new(err)))
                        }
                        _ => unreachable!(),
                    },
                }
            } else {
                break;
            }
        }
        None
    }
}
