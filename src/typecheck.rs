use std::collections::HashMap;
use std::rc::Rc;

use crate::errors::{Error, Result};
use crate::syntax::{name, BinOp, Decl, Name, Tm, Ty};

#[derive(Debug, Clone, Default)]
pub struct Env {
    tys: HashMap<Name, Rc<Ty>>,
    tyvars: Vec<Name>,
    aliases: HashMap<Name, Rc<Ty>>,
}

impl Env {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind_term(&mut self, n: &Name, t: Rc<Ty>) {
        self.tys.insert(n.clone(), t);
    }

    pub fn bind_tyvar(&mut self, n: &Name) {
        self.tyvars.push(n.clone());
    }

    pub fn pop_tyvar(&mut self) {
        self.tyvars.pop();
    }

    pub fn bind_alias(&mut self, n: &Name, t: Rc<Ty>) {
        self.aliases.insert(n.clone(), t);
    }

    fn lookup_term(&self, n: &Name) -> Option<Rc<Ty>> {
        self.tys.get(n).cloned()
    }

    fn is_tyvar(&self, n: &Name) -> bool {
        self.tyvars.iter().any(|v| v == n)
    }

    fn lookup_alias(&self, n: &Name) -> Option<Rc<Ty>> {
        self.aliases.get(n).cloned()
    }
}

#[must_use]
pub fn resolve(env: &Env, t: &Ty) -> Ty {
    match t {
        Ty::Var(n) => {
            if env.is_tyvar(n) {
                Ty::Var(n.clone())
            } else if let Some(a) = env.lookup_alias(n) {
                resolve(env, &a)
            } else {
                Ty::Var(n.clone())
            }
        }
        Ty::Arr(a, b) => Ty::Arr(Rc::new(resolve(env, a)), Rc::new(resolve(env, b))),
        Ty::Forall(x, body) => Ty::Forall(x.clone(), Rc::new(resolve(env, body))),
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
    }
}

fn subst(target: &Name, with: &Ty, in_: &Ty) -> Ty {
    match in_ {
        Ty::Var(n) if n == target => with.clone(),
        Ty::Var(n) => Ty::Var(n.clone()),
        Ty::Arr(a, b) => Ty::Arr(
            Rc::new(subst(target, with, a)),
            Rc::new(subst(target, with, b)),
        ),
        Ty::Forall(x, _) if x == target => in_.clone(),
        Ty::Forall(x, body) => Ty::Forall(x.clone(), Rc::new(subst(target, with, body))),
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
    }
}

fn alpha_eq(left: &Ty, right: &Ty) -> bool {
    fn go(left: &Ty, right: &Ty, ls: &mut Vec<Name>, rs: &mut Vec<Name>) -> bool {
        match (left, right) {
            (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) => true,
            (Ty::Var(lv), Ty::Var(rv)) => {
                let li = ls.iter().rev().position(|n| n == lv);
                let ri = rs.iter().rev().position(|n| n == rv);
                match (li, ri) {
                    (Some(a), Some(b)) => a == b,
                    (None, None) => lv == rv,
                    _ => false,
                }
            }
            (Ty::Arr(la, lb), Ty::Arr(ra, rb)) => go(la, ra, ls, rs) && go(lb, rb, ls, rs),
            (Ty::Forall(lv, lb), Ty::Forall(rv, rb)) => {
                ls.push(lv.clone());
                rs.push(rv.clone());
                let ok = go(lb, rb, ls, rs);
                ls.pop();
                rs.pop();
                ok
            }
            _ => false,
        }
    }
    go(left, right, &mut Vec::new(), &mut Vec::new())
}

fn well_formed(env: &Env, t: &Ty) -> Result<()> {
    match t {
        Ty::Int | Ty::Bool => Ok(()),
        Ty::Var(n) => {
            if env.is_tyvar(n) || env.lookup_alias(n).is_some() {
                Ok(())
            } else {
                Err(Error::Type(format!("unbound type variable: {n}")))
            }
        }
        Ty::Arr(a, b) => {
            well_formed(env, a)?;
            well_formed(env, b)
        }
        Ty::Forall(x, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(x);
            well_formed(&env2, body)
        }
    }
}

pub fn check(env: &mut Env, tm: &Tm, expected: &Ty) -> Result<()> {
    let got = infer(env, tm)?;
    let g = resolve(env, &got);
    let e = resolve(env, expected);
    if alpha_eq(&g, &e) {
        Ok(())
    } else {
        Err(Error::Type(format!(
            "type mismatch: expected {}, got {}",
            crate::pretty::ty(&e),
            crate::pretty::ty(&g)
        )))
    }
}

pub fn infer(env: &mut Env, tm: &Tm) -> Result<Ty> {
    match tm {
        Tm::Int(_) => Ok(Ty::Int),
        Tm::Bool(_) => Ok(Ty::Bool),
        Tm::Var(n) => env
            .lookup_term(n)
            .map(|t| (*t).clone())
            .ok_or_else(|| Error::Type(format!("unbound variable: {n}"))),
        Tm::Lam(x, ty, body) => {
            well_formed(env, ty)?;
            let mut env2 = env.clone();
            env2.bind_term(x, ty.clone());
            let body_ty = infer(&mut env2, body)?;
            Ok(Ty::Arr(ty.clone(), Rc::new(body_ty)))
        }
        Tm::App(f, x) => {
            let ft0 = infer(env, f)?;
            let ft = resolve(env, &ft0);
            match ft {
                Ty::Arr(a, b) => {
                    check(env, x, &a)?;
                    Ok((*b).clone())
                }
                other => Err(Error::Type(format!(
                    "expected function, got {}",
                    crate::pretty::ty(&other)
                ))),
            }
        }
        Tm::TLam(a, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(a);
            let bt = infer(&mut env2, body)?;
            Ok(Ty::Forall(a.clone(), Rc::new(bt)))
        }
        Tm::TApp(f, t) => {
            well_formed(env, t)?;
            let ft0 = infer(env, f)?;
            let ft = resolve(env, &ft0);
            match ft {
                Ty::Forall(a, body) => Ok(subst(&a, t, &body)),
                other => Err(Error::Type(format!(
                    "expected forall, got {}",
                    crate::pretty::ty(&other)
                ))),
            }
        }
        Tm::Let(x, ann, v, b) => {
            let vt = if let Some(a) = ann {
                well_formed(env, a)?;
                check(env, v, a)?;
                a.clone()
            } else {
                Rc::new(infer(env, v)?)
            };
            let mut env2 = env.clone();
            env2.bind_term(x, vt);
            infer(&mut env2, b)
        }
        Tm::If(c, t, e) => {
            check(env, c, &Ty::Bool)?;
            let tt = infer(env, t)?;
            check(env, e, &tt)?;
            Ok(tt)
        }
        Tm::Bin(op, l, r) => match op {
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                check(env, l, &Ty::Int)?;
                check(env, r, &Ty::Int)?;
                Ok(Ty::Int)
            }
            BinOp::Eq | BinOp::Lt => {
                check(env, l, &Ty::Int)?;
                check(env, r, &Ty::Int)?;
                Ok(Ty::Bool)
            }
            BinOp::And | BinOp::Or => {
                check(env, l, &Ty::Bool)?;
                check(env, r, &Ty::Bool)?;
                Ok(Ty::Bool)
            }
        },
        Tm::Fix(n, ty, body) => {
            well_formed(env, ty)?;
            let mut env2 = env.clone();
            env2.bind_term(n, ty.clone());
            check(&mut env2, body, ty)?;
            Ok((**ty).clone())
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
            well_formed(env, t)?;
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

#[must_use]
pub fn fresh(prefix: &str, used: &[Name]) -> Name {
    let mut i = 0;
    loop {
        let candidate = if i == 0 {
            prefix.to_string()
        } else {
            format!("{prefix}{i}")
        };
        let n = name(&candidate);
        if !used.iter().any(|u| **u == *n) {
            return n;
        }
        i += 1;
    }
}
