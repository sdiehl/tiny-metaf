use std::fmt::Write;

use unbound::prelude::*;

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
        Kind::Arr(a, b) => paren(out, prec, 0, |out| {
            write_kind(out, a, 1);
            out.push_str(" -> ");
            write_kind(out, b, 0);
        }),
    }
}

#[must_use]
pub fn ty(t: &Ty) -> String {
    let mut p = Printer::new(&t.fv());
    p.ty(t, 0);
    p.out
}

#[must_use]
pub fn tm(t: &Tm) -> String {
    let mut p = Printer::new(&t.fv());
    p.tm(t, 0);
    p.out
}

struct Printer {
    out: String,
    names: NameScope,
}

impl Printer {
    fn new(free: &[AnyName]) -> Self {
        Self {
            out: String::new(),
            names: NameScope::new(free),
        }
    }

    fn var<T>(&mut self, n: &Name<T>) {
        self.out.push_str(self.names.get(n));
    }

    fn binder(&mut self, n: &str, k: &Kind) {
        if matches!(k, Kind::Star) {
            self.out.push_str(n);
        } else {
            let _ = write!(self.out, "({n} : {})", kind(k));
        }
    }

    fn ty(&mut self, t: &Ty, prec: u8) {
        match t {
            Ty::Int => self.out.push_str("Int"),
            Ty::Bool => self.out.push_str("Bool"),
            Ty::Var(n) => self.var(n),
            Ty::Arr(a, b) => self.paren(prec, 0, |p| {
                p.ty(a, 1);
                p.out.push_str(" -> ");
                p.ty(b, 0);
            }),
            Ty::App(f, x) => self.paren(prec, 1, |p| {
                p.ty(f, 1);
                p.out.push(' ');
                p.ty(x, 2);
            }),
            Ty::Forall(bnd) | Ty::Lam(bnd) => {
                let kw = if matches!(t, Ty::Forall(_)) {
                    "forall"
                } else {
                    "lam"
                };
                let ((a, k), body) = bnd.unbind_ref();
                self.paren(prec, 0, |p| {
                    let d = p.names.bind(&a, &body.fv());
                    let _ = write!(p.out, "{kw} ");
                    p.binder(&d, &k);
                    p.out.push_str(". ");
                    p.ty(&body, 0);
                    p.names.pop();
                });
            }
        }
    }

    fn tm(&mut self, t: &Tm, prec: u8) {
        match t {
            Tm::Int(i) => {
                let _ = write!(self.out, "{i}");
            }
            Tm::Bool(b) => self.out.push_str(if *b { "true" } else { "false" }),
            Tm::Var(n) => self.var(n),
            Tm::Lam(b) => {
                let ((x, ty), body) = b.unbind_ref();
                self.paren(prec, 0, |p| {
                    let d = p.names.pick(&x, &body.fv());
                    let _ = write!(p.out, "\\({d} : ");
                    p.ty(&ty, 0);
                    p.names.push(&x, d);
                    p.out.push_str("). ");
                    p.tm(&body, 0);
                    p.names.pop();
                });
            }
            Tm::App(f, x) => self.paren(prec, 9, |p| {
                p.tm(f, 9);
                p.out.push(' ');
                p.tm(x, 10);
            }),
            Tm::TLam(bnd) => {
                let ((a, k), body) = bnd.unbind_ref();
                self.paren(prec, 0, |p| {
                    let d = p.names.bind(&a, &body.fv());
                    p.out.push_str("/\\");
                    p.binder(&d, &k);
                    p.out.push_str(". ");
                    p.tm(&body, 0);
                    p.names.pop();
                });
            }
            Tm::TApp(f, t) => self.paren(prec, 9, |p| {
                p.tm(f, 9);
                p.out.push_str(" [");
                p.ty(t, 0);
                p.out.push(']');
            }),
            Tm::Let(v, bnd) => {
                let ((x, ann), body) = bnd.unbind_ref();
                self.paren(prec, 0, |p| {
                    let d = p.names.pick(&x, &body.fv());
                    let _ = write!(p.out, "let {d}");
                    if let Some(a) = ann {
                        p.out.push_str(" : ");
                        p.ty(&a, 0);
                    }
                    p.out.push_str(" = ");
                    p.tm(v, 0);
                    p.out.push_str(" in ");
                    p.names.push(&x, d);
                    p.tm(&body, 0);
                    p.names.pop();
                });
            }
            Tm::If(c, th, el) => self.paren(prec, 0, |p| {
                p.out.push_str("if ");
                p.tm(c, 0);
                p.out.push_str(" then ");
                p.tm(th, 0);
                p.out.push_str(" else ");
                p.tm(el, 0);
            }),
            Tm::Bin(op, l, r) => {
                let o = op_prec(*op);
                self.paren(prec, o, |p| {
                    p.tm(l, o);
                    let _ = write!(p.out, " {op} ");
                    p.tm(r, o + 1);
                });
            }
            Tm::Ann(e, t) => self.paren(prec, 0, |p| {
                p.tm(e, 1);
                p.out.push_str(" : ");
                p.ty(t, 0);
            }),
        }
    }

    fn paren(&mut self, outer: u8, inner: u8, body: impl FnOnce(&mut Self)) {
        let needs = outer > inner;
        if needs {
            self.out.push('(');
        }
        body(self);
        if needs {
            self.out.push(')');
        }
    }
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
    }
}
