use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

use tiny_fself::driver::Session;
use tiny_fself::repl;

#[derive(Parser)]
#[command(name = "tiny-fself", about = "System F with a typed self-interpreter")]
struct Cli {
    #[command(subcommand)]
    cmd: Option<Cmd>,
}

#[derive(Subcommand)]
enum Cmd {
    Repl,
    Run { file: PathBuf },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let result = match cli.cmd.unwrap_or(Cmd::Repl) {
        Cmd::Repl => repl::run(),
        Cmd::Run { file } => {
            let mut s = Session::new();
            repl::load_file(&mut s, &file)
        }
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
