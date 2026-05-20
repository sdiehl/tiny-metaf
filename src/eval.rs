use std::collections::HashMap;
use std::rc::Rc;

use crate::errors::{Error, Result};
use crate::syntax::{BinOp, Name, Tm};

#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Closure(Env, Name, Rc<Tm>),
    TClosure(Env, Rc<Tm>),
    FixMarker(Env, Name, Rc<Tm>),
}

#[derive(Debug, Clone, Default)]
pub struct Env {
    vals: HashMap<Name, Rc<Value>>,
}

impl Env {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, n: &Name, v: Value) {
        self.vals.insert(n.clone(), Rc::new(v));
    }

    fn get(&self, n: &Name) -> Option<Rc<Value>> {
        self.vals.get(n).cloned()
    }
}

fn lookup(env: &Env, x: &Name) -> Result<Value> {
    env.get(x).map_or_else(
        || Err(Error::Runtime(format!("unbound variable: {x}"))),
        |v| match &*v {
            Value::FixMarker(env_cap, n, body) => {
                let mut e = env_cap.clone();
                e.bind(
                    n,
                    Value::FixMarker(env_cap.clone(), n.clone(), body.clone()),
                );
                eval(&e, body)
            }
            other => Ok(other.clone()),
        },
    )
}

pub fn eval(env: &Env, tm: &Tm) -> Result<Value> {
    match tm {
        Tm::Int(i) => Ok(Value::Int(*i)),
        Tm::Bool(b) => Ok(Value::Bool(*b)),
        Tm::Var(x) => lookup(env, x),
        Tm::Lam(x, _, body) => Ok(Value::Closure(env.clone(), x.clone(), body.clone())),
        Tm::TLam(_, body) => Ok(Value::TClosure(env.clone(), body.clone())),
        Tm::App(f, x) => {
            let fv = eval(env, f)?;
            let xv = eval(env, x)?;
            apply(fv, xv)
        }
        Tm::TApp(f, _) => {
            let fv = eval(env, f)?;
            match fv {
                Value::TClosure(env2, body) => eval(&env2, &body),
                _ => Err(Error::Runtime("expected type abstraction".into())),
            }
        }
        Tm::Let(x, _, v, b) => {
            let vv = eval(env, v)?;
            let mut env2 = env.clone();
            env2.bind(x, vv);
            eval(&env2, b)
        }
        Tm::If(c, t, e) => match eval(env, c)? {
            Value::Bool(true) => eval(env, t),
            Value::Bool(false) => eval(env, e),
            _ => Err(Error::Runtime("if condition not boolean".into())),
        },
        Tm::Bin(op, l, r) => {
            let lv = eval(env, l)?;
            let rv = eval(env, r)?;
            apply_bin(*op, &lv, &rv)
        }
        Tm::Fix(n, _, body) => {
            let mut env2 = env.clone();
            env2.bind(n, Value::FixMarker(env.clone(), n.clone(), body.clone()));
            eval(&env2, body)
        }
        Tm::Ann(e, _) => eval(env, e),
    }
}

fn apply(f: Value, x: Value) -> Result<Value> {
    match f {
        Value::Closure(env, n, body) => {
            let mut env2 = env;
            env2.bind(&n, x);
            eval(&env2, &body)
        }
        _ => Err(Error::Runtime("application of non-function".into())),
    }
}

fn apply_bin(op: BinOp, l: &Value, r: &Value) -> Result<Value> {
    match (op, l, r) {
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a + b)),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a - b)),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
        (BinOp::Eq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a == b)),
        (BinOp::Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
        (BinOp::And, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a && *b)),
        (BinOp::Or, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a || *b)),
        _ => Err(Error::Runtime(format!("bad operands for {op}"))),
    }
}
