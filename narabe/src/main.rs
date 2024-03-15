mod board;
use board::Board;
use protocol::{ManagerCommand, ManagerCommandReader};
use std::io;
use std::io::Write;

pub struct BrainClient<R, W: Write>
where
    R: Iterator,
    R::Item: AsRef<str>,
{
    ostream: W,
    istream: ManagerCommandReader<R>,
}

impl<R, W> BrainClient<R, W>
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
        self.ostream.write_all(s.as_bytes()).unwrap();
    }
}

impl<R, W> Iterator for BrainClient<R, W>
where
    R: Iterator,
    R::Item: AsRef<str>,
    W: Write,
{
    type Item = ManagerCommand;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(cmd) = self.istream.next() {
            match cmd {
                Ok(cmd) => return Some(cmd),
                Err(_) => self.error("invalid command"),
            }
        }
        None
    }
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
            }
            ManagerCommand::Start(_) => {
                client.error("unsupported board size");
            }
            ManagerCommand::Begin if initialized => {
            }
            ManagerCommand::Begin => client.error("board size not set"),
            _ => todo!(),
        }
    }
}
