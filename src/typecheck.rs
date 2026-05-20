use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::errors::{Error, Result};
use crate::pretty;
use crate::syntax::{name, BinOp, Decl, Kind, Name, Tm, Ty};

#[derive(Debug, Clone, Default)]
pub struct Env {
    tys: HashMap<Name, Rc<Ty>>,
    tyvars: Vec<(Name, Rc<Kind>)>,
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

    pub fn bind_tyvar(&mut self, n: &Name, k: Rc<Kind>) {
        self.tyvars.push((n.clone(), k));
    }

    pub fn bind_alias(&mut self, n: &Name, t: Rc<Ty>) {
        self.aliases.insert(n.clone(), t);
    }

    fn lookup_term(&self, n: &Name) -> Option<Rc<Ty>> {
        self.tys.get(n).cloned()
    }

    fn lookup_kind(&self, n: &Name) -> Option<Rc<Kind>> {
        self.tyvars
            .iter()
            .rev()
            .find(|(m, _)| m == n)
            .map(|(_, k)| k.clone())
    }

    fn lookup_alias(&self, n: &Name) -> Option<Rc<Ty>> {
        self.aliases.get(n).cloned()
    }
}

fn free_vars(t: &Ty) -> HashSet<Name> {
    fn go(t: &Ty, acc: &mut HashSet<Name>, bound: &mut Vec<Name>) {
        match t {
            Ty::Int | Ty::Bool => {}
            Ty::Var(n) => {
                if !bound.iter().any(|b| b == n) {
                    acc.insert(n.clone());
                }
            }
            Ty::Arr(a, b) | Ty::App(a, b) => {
                go(a, acc, bound);
                go(b, acc, bound);
            }
            Ty::Forall(x, _, body) | Ty::Lam(x, _, body) => {
                bound.push(x.clone());
                go(body, acc, bound);
                bound.pop();
            }
        }
    }
    let mut acc = HashSet::new();
    let mut bound = Vec::new();
    go(t, &mut acc, &mut bound);
    acc
}

fn subst(target: &Name, with: &Ty, in_: &Ty) -> Ty {
    let fv_with = free_vars(with);
    subst_inner(target, with, &fv_with, in_)
}

fn subst_inner(target: &Name, with: &Ty, fv_with: &HashSet<Name>, in_: &Ty) -> Ty {
    match in_ {
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
        Ty::Var(n) if n == target => with.clone(),
        Ty::Var(n) => Ty::Var(n.clone()),
        Ty::Arr(a, b) => Ty::Arr(
            Rc::new(subst_inner(target, with, fv_with, a)),
            Rc::new(subst_inner(target, with, fv_with, b)),
        ),
        Ty::App(a, b) => Ty::App(
            Rc::new(subst_inner(target, with, fv_with, a)),
            Rc::new(subst_inner(target, with, fv_with, b)),
        ),
        Ty::Forall(x, k, body) => {
            if x == target {
                in_.clone()
            } else if fv_with.contains(x) {
                let (x_new, body_new) = rename_binder(x, body, fv_with, target);
                let body_subbed = subst_inner(target, with, fv_with, &body_new);
                Ty::Forall(x_new, k.clone(), Rc::new(body_subbed))
            } else {
                Ty::Forall(
                    x.clone(),
                    k.clone(),
                    Rc::new(subst_inner(target, with, fv_with, body)),
                )
            }
        }
        Ty::Lam(x, k, body) => {
            if x == target {
                in_.clone()
            } else if fv_with.contains(x) {
                let (x_new, body_new) = rename_binder(x, body, fv_with, target);
                let body_subbed = subst_inner(target, with, fv_with, &body_new);
                Ty::Lam(x_new, k.clone(), Rc::new(body_subbed))
            } else {
                Ty::Lam(
                    x.clone(),
                    k.clone(),
                    Rc::new(subst_inner(target, with, fv_with, body)),
                )
            }
        }
    }
}

fn rename_binder(x: &Name, body: &Ty, fv_with: &HashSet<Name>, target: &Name) -> (Name, Ty) {
    let mut used: Vec<Name> = fv_with.iter().cloned().collect();
    used.extend(free_vars(body));
    used.push(target.clone());
    let x_new = fresh(x, &used);
    let body_new = subst(x, &Ty::Var(x_new.clone()), body);
    (x_new, body_new)
}

fn whnf(env: &Env, t: &Ty) -> Ty {
    match t {
        Ty::Var(n) => {
            if env.lookup_kind(n).is_some() {
                t.clone()
            } else if let Some(a) = env.lookup_alias(n) {
                whnf(env, &a)
            } else {
                t.clone()
            }
        }
        Ty::App(f, x) => match whnf(env, f) {
            Ty::Lam(a, _, body) => {
                let red = subst(&a, x, &body);
                whnf(env, &red)
            }
            other => Ty::App(Rc::new(other), x.clone()),
        },
        _ => t.clone(),
    }
}

fn nf(env: &Env, t: &Ty) -> Ty {
    match whnf(env, t) {
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
        Ty::Var(n) => Ty::Var(n),
        Ty::Arr(a, b) => Ty::Arr(Rc::new(nf(env, &a)), Rc::new(nf(env, &b))),
        Ty::Forall(x, k, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(&x, k.clone());
            Ty::Forall(x, k, Rc::new(nf(&env2, &body)))
        }
        Ty::Lam(x, k, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(&x, k.clone());
            Ty::Lam(x, k, Rc::new(nf(&env2, &body)))
        }
        Ty::App(f, x) => Ty::App(Rc::new(nf(env, &f)), Rc::new(nf(env, &x))),
    }
}

fn types_equal(env: &Env, a: &Ty, b: &Ty) -> bool {
    alpha_eq(&nf(env, a), &nf(env, b))
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
            (Ty::Arr(la, lb), Ty::Arr(ra, rb)) | (Ty::App(la, lb), Ty::App(ra, rb)) => {
                go(la, ra, ls, rs) && go(lb, rb, ls, rs)
            }
            (Ty::Forall(lv, lk, lb), Ty::Forall(rv, rk, rb))
            | (Ty::Lam(lv, lk, lb), Ty::Lam(rv, rk, rb)) => {
                if lk != rk {
                    return false;
                }
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

fn kind_of(env: &Env, ty: &Ty) -> Result<Kind> {
    match ty {
        Ty::Int | Ty::Bool => Ok(Kind::Star),
        Ty::Var(n) => env.lookup_kind(n).map_or_else(
            || {
                env.lookup_alias(n).map_or_else(
                    || Err(Error::Type(format!("unbound type variable: {n}"))),
                    |a| kind_of(env, &a),
                )
            },
            |k| Ok((*k).clone()),
        ),
        Ty::Arr(a, b) => {
            check_kind(env, a, &Kind::Star)?;
            check_kind(env, b, &Kind::Star)?;
            Ok(Kind::Star)
        }
        Ty::Forall(x, k, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(x, k.clone());
            check_kind(&env2, body, &Kind::Star)?;
            Ok(Kind::Star)
        }
        Ty::Lam(x, k, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(x, k.clone());
            let body_k = kind_of(&env2, body)?;
            Ok(Kind::Arr(k.clone(), Rc::new(body_k)))
        }
        Ty::App(f, x) => {
            let fk = kind_of(env, f)?;
            if let Kind::Arr(dom, cod) = fk {
                check_kind(env, x, &dom)?;
                Ok((*cod).clone())
            } else {
                Err(Error::Type(format!(
                    "expected type-level function kind, got {}",
                    pretty::kind(&fk)
                )))
            }
        }
    }
}

fn check_kind(env: &Env, t: &Ty, expected: &Kind) -> Result<()> {
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

fn well_formed(env: &Env, t: &Ty) -> Result<()> {
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
            let ft = whnf(env, &ft0);
            match ft {
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
        Tm::TLam(a, k, body) => {
            let mut env2 = env.clone();
            env2.bind_tyvar(a, k.clone());
            let bt = infer(&mut env2, body)?;
            Ok(Ty::Forall(a.clone(), k.clone(), Rc::new(bt)))
        }
        Tm::TApp(f, t) => {
            let ft0 = infer(env, f)?;
            let ft = whnf(env, &ft0);
            match ft {
                Ty::Forall(a, k, body) => {
                    check_kind(env, t, &k)?;
                    Ok(subst(&a, t, &body))
                }
                other => Err(Error::Type(format!(
                    "expected forall, got {}",
                    pretty::ty(&other)
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
