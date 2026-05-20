use std::rc::Rc;

use lalrpop_util::lalrpop_mod;

use crate::errors::{Error, Result};
use crate::lexer::Lexer;
use crate::syntax::{Decl, ReplItem, Tm, Ty};

lalrpop_mod!(
    #[allow(
        clippy::all,
        clippy::pedantic,
        clippy::nursery,
        dead_code,
        unreachable_pub
    )]
    parser
);

pub fn parse_program(src: &str) -> Result<Vec<Decl>> {
    parser::ProgramParser::new()
        .parse(Lexer::new(src))
        .map_err(|e| Error::Parse(e.to_string()))
}

pub fn parse_expr(src: &str) -> Result<Tm> {
    parser::ExprParser::new()
        .parse(Lexer::new(src))
        .map_err(|e| Error::Parse(e.to_string()))
}

pub fn parse_type(src: &str) -> Result<Ty> {
    parser::TypeParser::new()
        .parse(Lexer::new(src))
        .map_err(|e| Error::Parse(e.to_string()))
}

pub fn parse_repl(src: &str) -> Result<ReplItem> {
    if let Ok(ds) = parser::ProgramParser::new().parse(Lexer::new(src)) {
        if ds.len() == 1 {
            return Ok(ReplItem::Decl(ds.into_iter().next().unwrap()));
        }
    }
    let e = parse_expr(src)?;
    Ok(ReplItem::Expr(Rc::new(e)))
}
