use std::rc::Rc;

use crate::errors::Result;
use crate::eval::{self, Value};
use crate::pretty;
use crate::syntax::{Decl, Tm, Ty};
use crate::typecheck;

#[derive(Debug, Default)]
pub struct Session {
    pub tenv: typecheck::Env,
    pub venv: eval::Env,
}

impl Session {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn process_decl(&mut self, d: &Decl) -> Result<Option<String>> {
        typecheck::check_decl(&mut self.tenv, d)?;
        match d {
            Decl::TypeAlias(n, t) => Ok(Some(format!("type {n} = {}", pretty::ty(t)))),
            Decl::Let(n, t, body) => {
                let v = eval::eval(&self.venv, body)?;
                self.venv.bind(n, v);
                Ok(Some(format!("{n} : {}", pretty::ty(t))))
            }
            Decl::Eval(e) => {
                let v = eval::eval(&self.venv, e)?;
                Ok(Some(pretty::value(&v)))
            }
        }
    }

    pub fn process_program(&mut self, ds: &[Decl]) -> Result<Vec<String>> {
        let mut out = Vec::new();
        for d in ds {
            if let Some(s) = self.process_decl(d)? {
                out.push(s);
            }
        }
        Ok(out)
    }

    pub fn infer(&mut self, e: &Tm) -> Result<Ty> {
        typecheck::infer(&mut self.tenv, e)
    }

    pub fn eval_expr(&mut self, e: &Rc<Tm>) -> Result<(Ty, Value)> {
        let t = self.infer(e)?;
        let v = eval::eval(&self.venv, e)?;
        Ok((t, v))
    }
}
