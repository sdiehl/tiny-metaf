use std::fs;
use std::path::Path;

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use crate::driver::Session;
use crate::errors::Result;
use crate::parse;
use crate::pretty;
use crate::syntax::ReplItem;

const BANNER: &str = "tiny-fself  --  :? for help, :q to quit";

const HELP: &str = "\
commands:
  :t <expr>     show type of expression
  :l <file>     load and run a file
  :q            quit
  :?            this help

declarations end in ';'. examples:
  let id : forall a. a -> a = /\\a. \\(x:a). x;
  type Nat = forall a. (a -> a) -> a -> a;
  eval id [Int] 42;
";

pub fn run() -> Result<()> {
    let mut s = Session::new();
    let mut rl = DefaultEditor::new().map_err(|e| crate::errors::Error::Runtime(e.to_string()))?;
    println!("{BANNER}");
    loop {
        match rl.readline("fself> ") {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str());
                let trimmed = line.trim();
                if trimmed.is_empty() {
                    continue;
                }
                if let Some(rest) = trimmed.strip_prefix(':') {
                    if let Err(e) = handle_cmd(&mut s, rest) {
                        eprintln!("{e}");
                    }
                    if rest == "q" || rest.starts_with("q ") {
                        return Ok(());
                    }
                } else if let Err(e) = handle_input(&mut s, trimmed) {
                    eprintln!("{e}");
                }
            }
            Err(ReadlineError::Interrupted | ReadlineError::Eof) => return Ok(()),
            Err(e) => return Err(crate::errors::Error::Runtime(e.to_string())),
        }
    }
}

fn handle_cmd(s: &mut Session, cmd: &str) -> Result<()> {
    let (head, tail) = cmd.split_once(' ').unwrap_or((cmd, ""));
    let tail = tail.trim();
    match head {
        "q" | "quit" => Ok(()),
        "?" | "h" | "help" => {
            print!("{HELP}");
            Ok(())
        }
        "t" | "type" => {
            let e = parse::parse_expr(tail)?;
            let t = s.infer(&e)?;
            println!("{} : {}", pretty::tm(&e), pretty::ty(&t));
            Ok(())
        }
        "l" | "load" => load_file(s, Path::new(tail)),
        other => Err(crate::errors::Error::Runtime(format!(
            "unknown command: :{other}"
        ))),
    }
}

fn handle_input(s: &mut Session, src: &str) -> Result<()> {
    let item = parse::parse_repl(src)?;
    match item {
        ReplItem::Decl(d) => {
            if let Some(line) = s.process_decl(&d)? {
                println!("{line}");
            }
        }
        ReplItem::Expr(e) => {
            let (t, v) = s.eval_expr(&e)?;
            println!("{} : {}", pretty::value(&v), pretty::ty(&t));
        }
    }
    Ok(())
}

pub fn load_file(s: &mut Session, path: &Path) -> Result<()> {
    let src = fs::read_to_string(path)
        .map_err(|e| crate::errors::Error::Runtime(format!("{}: {e}", path.display())))?;
    let prog = parse::parse_program(&src)?;
    for line in s.process_program(&prog)? {
        println!("{line}");
    }
    Ok(())
}
