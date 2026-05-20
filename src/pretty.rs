use std::fmt::Write;

use crate::eval::Value;
use crate::syntax::{BinOp, Kind, Tm, Ty};

#[must_use]
pub fn kind(k: &Kind) -> String {
    let mut s = String::new();
    write_kind(&mut s, k, 0);
    s
}

fn write_kind(out: &mut String, k: &Kind, prec: u8) {
    match k {
        Kind::Star => out.push('*'),
        Kind::Arr(a, b) => {
            let needs = prec > 0;
            if needs {
                out.push('(');
            }
            write_kind(out, a, 1);
            out.push_str(" -> ");
            write_kind(out, b, 0);
            if needs {
                out.push(')');
            }
        }
    }
}

#[must_use]
pub fn ty(t: &Ty) -> String {
    let mut s = String::new();
    write_ty(&mut s, t, 0);
    s
}

fn write_ty(out: &mut String, t: &Ty, prec: u8) {
    match t {
        Ty::Int => out.push_str("Int"),
        Ty::Bool => out.push_str("Bool"),
        Ty::Var(n) => out.push_str(n),
        Ty::Arr(a, b) => {
            let needs = prec > 0;
            if needs {
                out.push('(');
            }
            write_ty(out, a, 1);
            out.push_str(" -> ");
            write_ty(out, b, 0);
            if needs {
                out.push(')');
            }
        }
        Ty::App(f, x) => {
            let needs = prec > 1;
            if needs {
                out.push('(');
            }
            write_ty(out, f, 1);
            out.push(' ');
            write_ty(out, x, 2);
            if needs {
                out.push(')');
            }
        }
        Ty::Forall(n, k, body) => {
            let needs = prec > 0;
            if needs {
                out.push('(');
            }
            if matches!(**k, Kind::Star) {
                let _ = write!(out, "forall {n}. ");
            } else {
                let _ = write!(out, "forall ({n} : {}). ", kind(k));
            }
            write_ty(out, body, 0);
            if needs {
                out.push(')');
            }
        }
        Ty::Lam(n, k, body) => {
            let needs = prec > 0;
            if needs {
                out.push('(');
            }
            if matches!(**k, Kind::Star) {
                let _ = write!(out, "lam {n}. ");
            } else {
                let _ = write!(out, "lam ({n} : {}). ", kind(k));
            }
            write_ty(out, body, 0);
            if needs {
                out.push(')');
            }
        }
    }
}

#[must_use]
pub fn tm(t: &Tm) -> String {
    let mut s = String::new();
    write_tm(&mut s, t, 0);
    s
}

const fn op_prec(op: BinOp) -> u8 {
    match op {
        BinOp::Or => 1,
        BinOp::And => 2,
        BinOp::Eq | BinOp::Lt => 3,
        BinOp::Add | BinOp::Sub => 4,
        BinOp::Mul => 5,
    }
}

fn write_tm(out: &mut String, t: &Tm, prec: u8) {
    match t {
        Tm::Int(i) => {
            let _ = write!(out, "{i}");
        }
        Tm::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Tm::Var(n) => out.push_str(n),
        Tm::Lam(x, t, body) => {
            paren(out, prec, 0, |out| {
                let _ = write!(out, "\\({x} : ");
                write_ty(out, t, 0);
                out.push_str("). ");
                write_tm(out, body, 0);
            });
        }
        Tm::App(f, x) => {
            paren(out, prec, 9, |out| {
                write_tm(out, f, 9);
                out.push(' ');
                write_tm(out, x, 10);
            });
        }
        Tm::TLam(a, k, body) => {
            paren(out, prec, 0, |out| {
                if matches!(**k, Kind::Star) {
                    let _ = write!(out, "/\\{a}. ");
                } else {
                    let _ = write!(out, "/\\({a} : {}). ", kind(k));
                }
                write_tm(out, body, 0);
            });
        }
        Tm::TApp(f, t) => {
            paren(out, prec, 9, |out| {
                write_tm(out, f, 9);
                out.push_str(" [");
                write_ty(out, t, 0);
                out.push(']');
            });
        }
        Tm::Let(x, ann, v, b) => {
            paren(out, prec, 0, |out| {
                let _ = write!(out, "let {x}");
                if let Some(a) = ann {
                    out.push_str(" : ");
                    write_ty(out, a, 0);
                }
                out.push_str(" = ");
                write_tm(out, v, 0);
                out.push_str(" in ");
                write_tm(out, b, 0);
            });
        }
        Tm::If(c, th, el) => {
            paren(out, prec, 0, |out| {
                out.push_str("if ");
                write_tm(out, c, 0);
                out.push_str(" then ");
                write_tm(out, th, 0);
                out.push_str(" else ");
                write_tm(out, el, 0);
            });
        }
        Tm::Bin(op, l, r) => {
            let p = op_prec(*op);
            paren(out, prec, p, |out| {
                write_tm(out, l, p);
                let _ = write!(out, " {op} ");
                write_tm(out, r, p + 1);
            });
        }
        Tm::Fix(n, t, body) => {
            paren(out, prec, 0, |out| {
                let _ = write!(out, "fix {n} : ");
                write_ty(out, t, 0);
                out.push_str(". ");
                write_tm(out, body, 0);
            });
        }
        Tm::Ann(e, t) => {
            paren(out, prec, 0, |out| {
                write_tm(out, e, 1);
                out.push_str(" : ");
                write_ty(out, t, 0);
            });
        }
    }
}

fn paren(out: &mut String, outer: u8, inner: u8, body: impl FnOnce(&mut String)) {
    let needs = outer > inner;
    if needs {
        out.push('(');
    }
    body(out);
    if needs {
        out.push(')');
    }
}

#[must_use]
pub fn value(v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Closure(..) => "<closure>".into(),
        Value::TClosure(..) => "<tclosure>".into(),
        Value::FixMarker(..) => "<fix>".into(),
    }
}
