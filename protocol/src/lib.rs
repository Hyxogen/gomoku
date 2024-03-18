use nom::bytes::complete::tag_no_case;
use nom::character::streaming;
use nom::sequence::{delimited, preceded, Tuple};
use nom::IResult;
use std::borrow::Cow;
use tools::Pos;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Field {
    Mine,
    Theirs,
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum ManagerCommand<'a> {
    Start(usize),
    Turn(Pos),
    Begin,
    Board(Cow<'a, Vec<(Pos, Field)>>),
    YXBoard(Cow<'a, Vec<(Pos, Field)>>),
    YXShowForbid,
    Info(String, String),
    End,
    About,
}

impl<'a> std::fmt::Display for ManagerCommand<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Start(size) => write!(f, "START {}", size),
            Self::Turn(pos) => write!(f, "TURN {},{}", pos.col(), pos.row()),
            Self::Begin => write!(f, "BEGIN"),
            Self::Board(pieces) | Self::YXBoard(pieces) => {
                if let Self::Board(_) = self {
                    writeln!(f, "BOARD")?;
                } else {
                    writeln!(f, "yxboard")?;
                }

                for (pos, field) in pieces.as_ref() {
                    writeln!(
                        f,
                        "{},{},{}",
                        pos.col(),
                        pos.row(),
                        if *field == Field::Mine { 1 } else { 2 }
                    )?;
                }
                write!(f, "DONE")
            }
            Self::YXShowForbid => write!(f, "yxshowforbid"),
            Self::Info(key, val) => write!(f, "INFO {} {}", key, val),
            Self::End => write!(f, "END"),
            Self::About => write!(f, "ABOUT"),
        }
    }
}

fn space0_line_ending(s: &str) -> IResult<&str, ()> {
    let (rem, _) = (streaming::space0, streaming::line_ending).parse(s)?;
    Ok((rem, ()))
}

impl<'a> ManagerCommand<'a> {
    fn comma(s: &str) -> IResult<&str, char> {
        delimited(streaming::space0, streaming::one_of(","), streaming::space0)(s)
    }

    fn pos(s: &str) -> IResult<&str, Pos> {
        let (rem, (row, _, col)) = (streaming::u8, Self::comma, streaming::u8).parse(s)?;
        Ok((rem, (col, row).into()))
    }

    fn start<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, (_, _, size)) =
            (tag_no_case("start"), streaming::space1, streaming::u8).parse(s)?;
        Ok((rem, ManagerCommand::Start(size.into())))
    }

    fn turn<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, (_, _, pos)) = (tag_no_case("turn"), streaming::space1, Self::pos).parse(s)?;
        Ok((rem, ManagerCommand::Turn(pos)))
    }

    fn begin<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
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

    fn done(s: &str) -> IResult<&str, ()> {
        let (rem, _) = (tag_no_case("done"),).parse(s)?;
        Ok((rem, ()))
    }

    fn board_pieces(s: &str) -> IResult<&str, Vec<(Pos, Field)>> {
        let (rem, (pieces, _)) = nom::multi::many_till(Self::board_piece, Self::done)(s)?;
        Ok((rem, pieces))
    }

    fn board<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, (_, _, pieces)) =
            (tag_no_case("board"), space0_line_ending, Self::board_pieces).parse(s)?;
        Ok((rem, ManagerCommand::Board(Cow::Owned(pieces))))
    }

    fn yxboard<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, (_, _, pieces)) = (
            tag_no_case("yxboard"),
            space0_line_ending,
            Self::board_pieces,
        )
            .parse(s)?;
        Ok((rem, ManagerCommand::YXBoard(Cow::Owned(pieces))))
    }

    fn yxshowforbid<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, _) = tag_no_case("yxshowforbid")(s)?;
        Ok((rem, ManagerCommand::YXShowForbid))
    }

    fn command<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        nom::branch::alt((
            Self::start,
            Self::begin,
            Self::turn,
            Self::board,
            Self::yxboard,
            Self::yxshowforbid,
        ))(s)
    }

    fn parse<'b, 'c>(s: &'b str) -> IResult<&'b str, ManagerCommand<'c>> {
        let (rem, (_, command, _)) =
            (streaming::multispace0, Self::command, space0_line_ending).parse(s)?;
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

pub struct ManagerCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    inner: I,
    phantom: std::marker::PhantomData<&'a I>,
}

impl<'a, I> ManagerCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    pub fn new(inner: I) -> Self {
        Self { inner, phantom: Default::default() }
    }
}

impl<'a, I> Iterator for ManagerCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    type Item = Result<ManagerCommand<'a>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut cmd = String::new();

        loop {
            if let Some(line) = self.inner.next() {
                cmd.push_str(line.as_ref());
                cmd.push('\r');
                cmd.push('\n');

                match ManagerCommand::parse(&cmd) {
                    Ok((_, cmd)) => {
                        return Some(Ok(cmd))
                    },
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

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum BrainCommand<'a> {
    Forbid(Cow<'a, Vec<Pos>>),
    Unknown(Cow<'a, String>),
    Error(Cow<'a, String>),
    Message(Cow<'a, String>),
    Debug(Cow<'a, String>),
    Ack,
}

impl<'a> std::fmt::Display for BrainCommand<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Forbid(positions) => {
                write!(f, "FORBID ")?;
                for pos in positions.as_ref() {
                    write!(f, "{:0>2}{:0>2}", pos.col(), pos.row())?;
                }
                write!(f, ".")
            }
            Self::Unknown(msg) => write!(f, "UNKNOWN: {}", msg),
            Self::Error(msg) => write!(f, "ERROR: {}", msg),
            Self::Message(msg) => write!(f, "MESSAGE: {}", msg),
            Self::Debug(msg) => write!(f, "DEBUG: {}", msg),
            Self::Ack => write!(f, "OK"),
        }
    }
}

impl<'a> BrainCommand<'a> {
    fn digit(s: &str) -> IResult<&str, u8> {
        let (rem, digit) = streaming::one_of("0123456789")(s)?;
        //Unwrap will not fail, as digit is definitely a digit
        Ok((rem, digit.to_digit(10).unwrap() as u8))
    }

    fn pos_part(s: &str) -> IResult<&str, u8> {
        let (rem, (a, b)) = (Self::digit, Self::digit).parse(s)?;
        Ok((rem, a * 10 + b))
    }

    fn forbid_pos(s: &str) -> IResult<&str, Pos> {
        let (rem, (col, row)) = (Self::pos_part, Self::pos_part).parse(s)?;
        Ok((rem, (row, col).into()))
    }

    fn forbid_positions(s: &str) -> IResult<&str, Vec<Pos>> {
        let (rem, (positions, _)) =
            nom::multi::many_till(Self::forbid_pos, streaming::char('.'))(s)?;
        Ok((rem, positions))
    }

    fn any_command<T, Input, Error: nom::error::ParseError<Input>>(
        cmd: T,
    ) -> impl Fn(Input) -> IResult<Input, Input, Error>
    where
        Input: nom::InputTake + nom::InputLength + nom::Compare<T> + nom::InputTakeAtPosition,
        <Input as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
        T: nom::InputLength + Clone,
    {
        move |i: Input| nom::sequence::terminated(tag_no_case(cmd.clone()), streaming::space1)(i)
    }

    fn forbid<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, positions) = preceded(Self::any_command("forbid"), Self::forbid_positions)(s)?;
        Ok((rem, BrainCommand::Forbid(Cow::Owned(positions))))
    }

    fn any_msg<'b, 'c>(msg_type: &'b str) -> impl Fn(&'c str) -> IResult<&'c str, &'c str> + 'b {
        move |i: &str| preceded(Self::any_command(msg_type), streaming::not_line_ending)(i)
    }

    fn unknown<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, msg) = Self::any_msg("unknown")(s)?;
        Ok((rem, BrainCommand::Message(Cow::Owned(msg.to_string()))))
    }

    fn error<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, msg) = Self::any_msg("error")(s)?;
        Ok((rem, BrainCommand::Message(Cow::Owned(msg.to_string()))))
    }

    fn message<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, msg) = Self::any_msg("message")(s)?;
        Ok((rem, BrainCommand::Message(Cow::Owned(msg.to_string()))))
    }

    fn debug<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, msg) = Self::any_msg("debug")(s)?;
        Ok((rem, BrainCommand::Message(Cow::Owned(msg.to_string()))))
    }

    fn ack<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, _) = tag_no_case("ok")(s)?;
        Ok((rem, BrainCommand::Ack))
    }

    fn command<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        nom::branch::alt((
            Self::forbid,
            Self::unknown,
            Self::error,
            Self::message,
            Self::debug,
            Self::ack,
        ))(s)
    }

    fn parse<'b, 'c>(s: &'b str) -> IResult<&'b str, BrainCommand<'c>> {
        let (rem, (_, command, _)) =
            (streaming::space0, Self::command, space0_line_ending).parse(s)?;
        Ok((rem, command))
    }
}

pub struct BrainCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    inner: I,
    phantom: std::marker::PhantomData<&'a I>,
}

impl<'a, I> BrainCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    pub fn new(inner: I) -> Self {
        Self {
            inner,
            phantom: Default::default(),
        }
    }
}

impl<'a, I> Iterator for BrainCommandReader<'a, I>
where
    I: Iterator,
    I::Item: AsRef<str>,
{
    type Item = Result<BrainCommand<'a>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(line) = self.inner.next() {
            let mut line = line.as_ref().trim().to_string();
            line.push('\n');

            match BrainCommand::parse(&line) {
                Ok((_, cmd)) => Some(Ok(cmd)),
                Err(nom::Err::Incomplete(_)) => todo!(),
                Err(err) => match err.to_owned() {
                    nom::Err::Error(err) | nom::Err::Failure(err) => {
                        return Some(Err(ParseError::new(err)))
                    }
                    _ => unreachable!(),
                },
            }
        } else {
            None
        }
    }
}
