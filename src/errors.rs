use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("parse error: {0}")]
    Parse(String),
    #[error("type error: {0}")]
    Type(String),
    #[error("runtime error: {0}")]
    Runtime(String),
}

pub type Result<T> = std::result::Result<T, Error>;
