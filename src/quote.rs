//! Quoter: convert pure F-omega terms into their Brown-Palsberg deep
//! self-representation. Source fragment is Var/Lam/App/TLam/TApp; the result
//! is an `Exp [[t]]` value built from abs / app / tabs / tapp.

use std::rc::Rc;

use crate::errors::{Error, Result};
use crate::syntax::{name, Kind, Name, Tm, Ty};
use crate::typecheck::{self, subst};

const F: &str = "F";
const ABS: &str = "abs";
const APPC: &str = "app";
const TABS: &str = "tabs";
const TAPPC: &str = "tapp";

fn f_of(t: Ty) -> Ty {
    Ty::App(Rc::new(Ty::Var(name(F))), Rc::new(t))
}

/// Pre-representation of a source type. `F` is left free, to be bound by
/// `pre_rep_universe`.
#[must_use]
pub fn pre_rep(t: &Ty) -> Ty {
    match t {
        Ty::Int => Ty::Int,
        Ty::Bool => Ty::Bool,
        Ty::Var(n) => Ty::Var(n.clone()),
        Ty::Arr(a, b) => Ty::Arr(Rc::new(f_of(pre_rep(a))), Rc::new(f_of(pre_rep(b)))),
        Ty::Forall(a, k, body) => Ty::Forall(a.clone(), k.clone(), Rc::new(f_of(pre_rep(body)))),
        Ty::Lam(a, k, body) => Ty::Lam(a.clone(), k.clone(), Rc::new(pre_rep(body))),
        Ty::App(a, b) => Ty::App(Rc::new(pre_rep(a)), Rc::new(pre_rep(b))),
    }
}

/// Pre-representation universe: `lam F : * -> *. [[t]]`.
#[must_use]
pub fn pre_rep_universe(t: &Ty) -> Ty {
    Ty::Lam(
        name(F),
        Rc::new(Kind::Arr(Rc::new(Kind::Star), Rc::new(Kind::Star))),
        Rc::new(pre_rep(t)),
    )
}

/// Inhabitant of an arbitrary kind. `*` -> `forall a. a`; `k1 -> k2` ->
/// `lam (a : k1). inh(k2)`.
fn inh(k: &Kind) -> Ty {
    match k {
        Kind::Star => Ty::Forall(name("a"), Rc::new(Kind::Star), Rc::new(Ty::Var(name("a")))),
        Kind::Arr(k1, k2) => Ty::Lam(name("a"), k1.clone(), Rc::new(inh(k2))),
    }
}

/// Build the strip function for a `TLam (alpha : k). body : forall a:k. tau`.
/// Result has type `Strip F (forall a:k. F[[tau]])`.
fn strip_fn(alpha: &Name, k: &Kind, tau: &Ty) -> Tm {
    let inh_k = inh(k);
    let a_pre = pre_rep(tau);
    let body_ty = Ty::Forall(
        alpha.clone(),
        Rc::new(k.clone()),
        Rc::new(f_of(a_pre.clone())),
    );
    let gamma = subst(alpha, &inh_k, &a_pre);
    let f_ty = Ty::Forall(
        name("c"),
        Rc::new(Kind::Star),
        Rc::new(Ty::Arr(
            Rc::new(f_of(Ty::Var(name("c")))),
            Rc::new(Ty::Var(name("b"))),
        )),
    );
    let x = Tm::TApp(Rc::new(Tm::Var(name("x"))), Rc::new(inh_k));
    let body = Tm::App(
        Rc::new(Tm::TApp(Rc::new(Tm::Var(name("f"))), Rc::new(gamma))),
        Rc::new(x),
    );
    Tm::TLam(
        name("b"),
        Rc::new(Kind::Star),
        Rc::new(Tm::Lam(
            name("f"),
            Rc::new(f_ty),
            Rc::new(Tm::Lam(name("x"), Rc::new(body_ty), Rc::new(body))),
        )),
    )
}

/// Build the inst function for a `TApp e sigma` where `e : forall a:k. tau`.
/// Result has type `(forall a:k. F[[tau]]) -> F[[tau[sigma/a]]]`.
fn inst_fn(alpha: &Name, k: &Kind, tau: &Ty, sigma: &Ty) -> Tm {
    let a_pre = pre_rep(tau);
    let g_ty = Ty::Forall(alpha.clone(), Rc::new(k.clone()), Rc::new(f_of(a_pre)));
    Tm::Lam(
        name("g"),
        Rc::new(g_ty),
        Rc::new(Tm::TApp(
            Rc::new(Tm::Var(name("g"))),
            Rc::new(pre_rep(sigma)),
        )),
    )
}

fn rcty(t: Ty) -> Rc<Ty> {
    Rc::new(t)
}

fn rctm(t: Tm) -> Rc<Tm> {
    Rc::new(t)
}

/// Encode `tm` (of source type `ty`) into its deep representation.
///
/// The result type-checks against `Exp [[ty]]` in an environment exporting
/// the standard preamble (`Op`, `Strip`, `Abs`, `App`, `TAbs`, `TApp`, `Exp`).
pub fn quote(env: &typecheck::Env, tm: &Tm, ty: &Ty) -> Result<Tm> {
    let inner = quote_inner(&mut env.clone(), tm, ty)?;
    let f_kind = Kind::Arr(Rc::new(Kind::Star), Rc::new(Kind::Star));
    let abs_ty = Ty::App(Rc::new(Ty::Var(name("Abs"))), Rc::new(Ty::Var(name(F))));
    let app_ty = Ty::App(Rc::new(Ty::Var(name("App"))), Rc::new(Ty::Var(name(F))));
    let tabs_ty = Ty::App(Rc::new(Ty::Var(name("TAbs"))), Rc::new(Ty::Var(name(F))));
    let tapp_ty = Ty::App(Rc::new(Ty::Var(name("TApp"))), Rc::new(Ty::Var(name(F))));
    Ok(Tm::TLam(
        name(F),
        Rc::new(f_kind),
        rctm(Tm::Lam(
            name(ABS),
            rcty(abs_ty),
            rctm(Tm::Lam(
                name(APPC),
                rcty(app_ty),
                rctm(Tm::Lam(
                    name(TABS),
                    rcty(tabs_ty),
                    rctm(Tm::Lam(name(TAPPC), rcty(tapp_ty), rctm(inner))),
                )),
            )),
        )),
    ))
}

fn quote_inner(env: &mut typecheck::Env, tm: &Tm, ty: &Ty) -> Result<Tm> {
    match tm {
        Tm::Var(n) => Ok(Tm::Var(n.clone())),
        Tm::Lam(x, dom, body) => {
            let cod = match ty {
                Ty::Arr(_, c) => (**c).clone(),
                _ => return Err(Error::Type("quote: lambda needs arrow type".into())),
            };
            let mut env2 = env.clone();
            env2.bind_term(x, dom.clone());
            let qbody = quote_inner(&mut env2, body, &cod)?;
            let dom_pre = pre_rep(dom);
            let cod_pre = pre_rep(&cod);
            let inner_lam = Tm::Lam(x.clone(), rcty(f_of(dom_pre.clone())), rctm(qbody));
            Ok(Tm::App(
                rctm(Tm::TApp(
                    rctm(Tm::TApp(rctm(Tm::Var(name(ABS))), rcty(dom_pre))),
                    rcty(cod_pre),
                )),
                rctm(inner_lam),
            ))
        }
        Tm::App(f, x) => {
            let ft = typecheck::infer(env, f)?;
            let (dom, cod) = match &ft {
                Ty::Arr(a, b) => ((**a).clone(), (**b).clone()),
                _ => return Err(Error::Type("quote: application of non-function".into())),
            };
            let qf = quote_inner(env, f, &ft)?;
            let qx = quote_inner(env, x, &dom)?;
            let dom_pre = pre_rep(&dom);
            let cod_pre = pre_rep(&cod);
            Ok(Tm::App(
                rctm(Tm::App(
                    rctm(Tm::TApp(
                        rctm(Tm::TApp(rctm(Tm::Var(name(APPC))), rcty(dom_pre))),
                        rcty(cod_pre),
                    )),
                    rctm(qf),
                )),
                rctm(qx),
            ))
        }
        Tm::TLam(a, k, body) => {
            let body_ty = match ty {
                Ty::Forall(_, _, b) => (**b).clone(),
                _ => return Err(Error::Type("quote: type-lambda needs forall type".into())),
            };
            let mut env2 = env.clone();
            env2.bind_tyvar(a, k.clone());
            let qbody = quote_inner(&mut env2, body, &body_ty)?;
            let body_pre = pre_rep(&body_ty);
            let a_pre = Ty::Forall(a.clone(), k.clone(), rcty(f_of(body_pre)));
            let strip = strip_fn(a, k, &body_ty);
            let inner_tlam = Tm::TLam(a.clone(), k.clone(), rctm(qbody));
            Ok(Tm::App(
                rctm(Tm::App(
                    rctm(Tm::TApp(rctm(Tm::Var(name(TABS))), rcty(a_pre))),
                    rctm(strip),
                )),
                rctm(inner_tlam),
            ))
        }
        Tm::TApp(e, sigma) => {
            let et = typecheck::infer(env, e)?;
            let (alpha, k, tau) = match &et {
                Ty::Forall(a, k, b) => (a.clone(), (**k).clone(), (**b).clone()),
                _ => return Err(Error::Type("quote: type-application of non-forall".into())),
            };
            let qe = quote_inner(env, e, &et)?;
            let tau_pre = pre_rep(&tau);
            let a_ty = Ty::Forall(
                alpha.clone(),
                Rc::new(k.clone()),
                rcty(f_of(tau_pre.clone())),
            );
            let sigma_pre = pre_rep(sigma);
            let b_ty = subst(&alpha, &sigma_pre, &tau_pre);
            let inst = inst_fn(&alpha, &k, &tau, sigma);
            Ok(Tm::App(
                rctm(Tm::TApp(
                    rctm(Tm::App(
                        rctm(Tm::TApp(rctm(Tm::Var(name(TAPPC))), rcty(a_ty))),
                        rctm(qe),
                    )),
                    rcty(b_ty),
                )),
                rctm(inst),
            ))
        }
        Tm::Int(_)
        | Tm::Bool(_)
        | Tm::Let(..)
        | Tm::If(..)
        | Tm::Bin(..)
        | Tm::Fix(..)
        | Tm::Ann(..) => Err(Error::Type(
            "quote: only pure F-omega (var, lam, app, tlam, tapp) is supported".into(),
        )),
    }
}
