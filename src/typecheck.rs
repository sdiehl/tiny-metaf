use std::collections::HashMap;
use std::rc::Rc;

use unbound::prelude::*;

use crate::errors::{Error, Result};
use crate::pretty;
use crate::syntax::{BinOp, Decl, Kind, Tm, TmName, Ty, TyName};

/// Binders are opened with globally fresh names, so scopes never shadow and
/// entries can be added without ever being removed.
#[derive(Debug, Clone, Default)]
pub struct Env {
    tys: HashMap<TmName, Rc<Ty>>,
    kinds: HashMap<TyName, Kind>,
    aliases: HashMap<TyName, Rc<Ty>>,
}

impl Env {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind_term(&mut self, n: &TmName, t: Rc<Ty>) {
        self.tys.insert(n.clone(), t);
    }

    pub fn bind_tyvar(&mut self, n: &TyName, k: Kind) {
        self.kinds.insert(n.clone(), k);
    }

    pub fn bind_alias(&mut self, n: &TyName, t: Rc<Ty>) {
        self.aliases.insert(n.clone(), t);
    }

    #[must_use]
    pub fn is_alias(&self, n: &AnyName) -> bool {
        self.aliases.keys().any(|a| a == n)
    }
}

#[must_use]
pub fn whnf(env: &Env, t: &Ty) -> Ty {
    match t {
        Ty::Var(n) => env
            .aliases
            .get(n)
            .map_or_else(|| t.clone(), |a| whnf(env, a)),
        Ty::App(f, x) => match whnf(env, f) {
            Ty::Lam(b) => whnf(env, &b.instantiate(&**x)),
            other => Ty::App(Rc::new(other), x.clone()),
        },
        _ => t.clone(),
    }
}

#[must_use]
pub fn nf(env: &Env, t: &Ty) -> Ty {
    match whnf(env, t) {
        Ty::Arr(a, b) => Ty::arr(nf(env, &a), nf(env, &b)),
        Ty::App(f, x) => Ty::app(nf(env, &f), nf(env, &x)),
        Ty::Forall(b) => {
            let ((a, k), body) = b.unbind();
            Ty::forall(a, k, nf(env, &body))
        }
        Ty::Lam(b) => {
            let ((a, k), body) = b.unbind();
            Ty::lam(a, k, nf(env, &body))
        }
        t => t,
    }
}

fn types_equal(env: &Env, a: &Ty, b: &Ty) -> bool {
    nf(env, a).aeq(&nf(env, b))
}

fn kind_of(env: &mut Env, ty: &Ty) -> Result<Kind> {
    match ty {
        Ty::Int | Ty::Bool => Ok(Kind::Star),
        Ty::Var(n) => {
            if let Some(k) = env.kinds.get(n) {
                return Ok(k.clone());
            }
            let alias = env
                .aliases
                .get(n)
                .cloned()
                .ok_or_else(|| Error::Type(format!("unbound type variable: {n}")))?;
            kind_of(env, &alias)
        }
        Ty::Arr(a, b) => {
            check_kind(env, a, &Kind::Star)?;
            check_kind(env, b, &Kind::Star)?;
            Ok(Kind::Star)
        }
        Ty::Forall(b) => {
            let ((a, k), body) = b.unbind_ref();
            env.bind_tyvar(&a, k);
            check_kind(env, &body, &Kind::Star)?;
            Ok(Kind::Star)
        }
        Ty::Lam(b) => {
            let ((a, k), body) = b.unbind_ref();
            env.bind_tyvar(&a, k.clone());
            Ok(Kind::arr(k, kind_of(env, &body)?))
        }
        Ty::App(f, x) => match kind_of(env, f)? {
            Kind::Arr(dom, cod) => {
                check_kind(env, x, &dom)?;
                Ok((*cod).clone())
            }
            fk @ Kind::Star => Err(Error::Type(format!(
                "expected type-level function kind, got {}",
                pretty::kind(&fk)
            ))),
        },
    }
}

fn check_kind(env: &mut Env, t: &Ty, expected: &Kind) -> Result<()> {
    let got = kind_of(env, t)?;
    if got == *expected {
        Ok(())
    } else {
        Err(Error::Type(format!(
            "kind mismatch: expected {}, got {}",
            pretty::kind(expected),
            pretty::kind(&got)
        )))
    }
}

fn well_formed(env: &mut Env, t: &Ty) -> Result<()> {
    check_kind(env, t, &Kind::Star)
}

pub fn check(env: &mut Env, tm: &Tm, expected: &Ty) -> Result<()> {
    let got = infer(env, tm)?;
    if types_equal(env, &got, expected) {
        Ok(())
    } else {
        Err(Error::Type(format!(
            "type mismatch: expected {}, got {}",
            pretty::ty(&nf(env, expected)),
            pretty::ty(&nf(env, &got))
        )))
    }
}

pub fn infer(env: &mut Env, tm: &Tm) -> Result<Ty> {
    match tm {
        Tm::Int(_) => Ok(Ty::Int),
        Tm::Bool(_) => Ok(Ty::Bool),
        Tm::Var(n) => env
            .tys
            .get(n)
            .map(|t| (**t).clone())
            .ok_or_else(|| Error::Type(format!("unbound variable: {n}"))),
        Tm::Lam(b) => {
            let ((x, ty), body) = b.unbind_ref();
            well_formed(env, &ty)?;
            env.bind_term(&x, ty.clone());
            let body_ty = infer(env, &body)?;
            Ok(Ty::Arr(ty, Rc::new(body_ty)))
        }
        Tm::App(f, x) => {
            let ft = infer(env, f)?;
            match whnf(env, &ft) {
                Ty::Arr(a, b) => {
                    check(env, x, &a)?;
                    Ok((*b).clone())
                }
                other => Err(Error::Type(format!(
                    "expected function, got {}",
                    pretty::ty(&other)
                ))),
            }
        }
        Tm::TLam(b) => {
            let ((a, k), body) = b.unbind_ref();
            env.bind_tyvar(&a, k.clone());
            let bt = infer(env, &body)?;
            Ok(Ty::forall(a, k, bt))
        }
        Tm::TApp(f, t) => {
            let ft = infer(env, f)?;
            match whnf(env, &ft) {
                Ty::Forall(b) => {
                    check_kind(env, t, &b.pattern().1)?;
                    Ok(Rc::unwrap_or_clone(b.instantiate(&**t)))
                }
                other => Err(Error::Type(format!(
                    "expected forall, got {}",
                    pretty::ty(&other)
                ))),
            }
        }
        Tm::Let(v, b) => {
            let ((x, ann), body) = b.unbind_ref();
            let vt = if let Some(a) = ann {
                well_formed(env, &a)?;
                check(env, v, &a)?;
                a
            } else {
                Rc::new(infer(env, v)?)
            };
            env.bind_term(&x, vt);
            infer(env, &body)
        }
        Tm::If(c, t, e) => {
            check(env, c, &Ty::Bool)?;
            let tt = infer(env, t)?;
            check(env, e, &tt)?;
            Ok(tt)
        }
        Tm::Bin(op, l, r) => {
            let (arg, res) = match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul => (Ty::Int, Ty::Int),
                BinOp::Eq | BinOp::Lt => (Ty::Int, Ty::Bool),
                BinOp::And | BinOp::Or => (Ty::Bool, Ty::Bool),
            };
            check(env, l, &arg)?;
            check(env, r, &arg)?;
            Ok(res)
        }
        Tm::Fix(b) => {
            let ((n, ty), body) = b.unbind_ref();
            well_formed(env, &ty)?;
            env.bind_term(&n, ty.clone());
            check(env, &body, &ty)?;
            Ok((*ty).clone())
        }
        Tm::Ann(e, t) => {
            well_formed(env, t)?;
            check(env, e, t)?;
            Ok((**t).clone())
        }
    }
}

pub fn check_decl(env: &mut Env, d: &Decl) -> Result<()> {
    match d {
        Decl::TypeAlias(n, t) => {
            kind_of(env, t)?;
            env.bind_alias(n, t.clone());
            Ok(())
        }
        Decl::Let(n, t, body) => {
            well_formed(env, t)?;
            check(env, body, t)?;
            env.bind_term(n, t.clone());
            Ok(())
        }
        Decl::Eval(e) => {
            infer(env, e)?;
            Ok(())
        }
    }
}
