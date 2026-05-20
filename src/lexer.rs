use std::fmt;

use logos::{skip, Lexer as LogosLexer, Logos};
use thiserror::Error;

#[derive(Logos, Debug, Clone, PartialEq, Eq)]
pub enum Token {
    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("if")]
    If,
    #[token("then")]
    Then,
    #[token("else")]
    Else,
    #[token("true")]
    True,
    #[token("false")]
    False,
    #[token("forall")]
    Forall,
    #[token("Int")]
    IntTy,
    #[token("Bool")]
    BoolTy,
    #[token("type")]
    Type,
    #[token("eval")]
    Eval,
    #[token("fix")]
    Fix,
    #[token("lam")]
    Lam,

    #[token("->")]
    Arrow,
    #[token("=")]
    Eq,
    #[token("==")]
    EqEq,
    #[token("<")]
    Lt,
    #[token("&&")]
    AndAnd,
    #[token("||")]
    PipePipe,
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token(":")]
    Colon,
    #[token(";")]
    Semi,
    #[token(".")]
    Dot,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("[")]
    LBracket,
    #[token("]")]
    RBracket,
    #[token("\\")]
    Lambda,
    #[token("/\\")]
    BigLambda,

    #[regex(r"[0-9]+", |lex| lex.slice().parse::<i64>().ok())]
    Num(i64),
    #[regex(r"[a-zA-Z_][a-zA-Z0-9_']*", |lex| lex.slice().to_string())]
    Ident(String),

    #[regex(r"[ \t\n\r\f]+", skip)]
    #[regex(r"--[^\n\r]*", skip, allow_greedy = true)]
    Whitespace,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Let => write!(f, "let"),
            Self::In => write!(f, "in"),
            Self::If => write!(f, "if"),
            Self::Then => write!(f, "then"),
            Self::Else => write!(f, "else"),
            Self::True => write!(f, "true"),
            Self::False => write!(f, "false"),
            Self::Forall => write!(f, "forall"),
            Self::IntTy => write!(f, "Int"),
            Self::BoolTy => write!(f, "Bool"),
            Self::Type => write!(f, "type"),
            Self::Eval => write!(f, "eval"),
            Self::Fix => write!(f, "fix"),
            Self::Lam => write!(f, "lam"),
            Self::Arrow => write!(f, "->"),
            Self::Eq => write!(f, "="),
            Self::EqEq => write!(f, "=="),
            Self::Lt => write!(f, "<"),
            Self::AndAnd => write!(f, "&&"),
            Self::PipePipe => write!(f, "||"),
            Self::Plus => write!(f, "+"),
            Self::Minus => write!(f, "-"),
            Self::Star => write!(f, "*"),
            Self::Colon => write!(f, ":"),
            Self::Semi => write!(f, ";"),
            Self::Dot => write!(f, "."),
            Self::LParen => write!(f, "("),
            Self::RParen => write!(f, ")"),
            Self::LBracket => write!(f, "["),
            Self::RBracket => write!(f, "]"),
            Self::Lambda => write!(f, "\\"),
            Self::BigLambda => write!(f, "/\\"),
            Self::Num(n) => write!(f, "{n}"),
            Self::Ident(s) => write!(f, "{s}"),
            Self::Whitespace => write!(f, "<whitespace>"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LexicalError {
    #[error("invalid token at byte offset {0}")]
    InvalidToken(usize),
}

#[derive(Debug)]
pub struct Lexer<'input> {
    inner: LogosLexer<'input, Token>,
}

impl<'input> Lexer<'input> {
    #[must_use]
    pub fn new(input: &'input str) -> Self {
        Self {
            inner: Token::lexer(input),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<(usize, Token, usize), LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let tok = self.inner.next()?;
            let span = self.inner.span();
            return Some(match tok {
                Ok(Token::Whitespace) => continue,
                Ok(t) => Ok((span.start, t, span.end)),
                Err(()) => Err(LexicalError::InvalidToken(span.start)),
            });
        }
    }
}
