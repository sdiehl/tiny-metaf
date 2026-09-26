//! Quoter: convert pure F-omega terms into their Brown-Palsberg deep
//! self-representation. Source fragment is Var/Lam/App/TLam/TApp; the result
//! is an `Exp [[t]]` value built from abs / app / tabs / tapp.
//!
//! Every binder the quoter introduces is a globally fresh name, so nothing in
//! the source term can capture or be captured by it.

use unbound::prelude::*;

use crate::errors::{Error, Result};
use crate::syntax::{Kind, Tm, TmName, Ty, TyName};
use crate::typecheck::{self, nf};

fn star_to_star() -> Kind {
    Kind::arr(Kind::Star, Kind::Star)
}

fn at(f: &TyName, t: Ty) -> Ty {
    Ty::app(Ty::Var(f.clone()), t)
}

/// Pre-representation of a normalised source type, parametric in `f`.
#[must_use]
pub fn pre_rep(f: &TyName, t: &Ty) -> Ty {
    match t {
        Ty::Int | Ty::Bool | Ty::Var(_) => t.clone(),
        Ty::Arr(a, b) => Ty::arr(at(f, pre_rep(f, a)), at(f, pre_rep(f, b))),
        Ty::Forall(bnd) => {
            let ((a, k), body) = bnd.unbind_ref();
            Ty::forall(a, k, at(f, pre_rep(f, &body)))
        }
        Ty::Lam(bnd) => {
            let ((a, k), body) = bnd.unbind_ref();
            Ty::lam(a, k, pre_rep(f, &body))
        }
        Ty::App(a, b) => Ty::app(pre_rep(f, a), pre_rep(f, b)),
    }
}

/// Pre-representation universe: `lam F : * -> *. [[t]]`.
#[must_use]
pub fn pre_rep_universe(t: &Ty) -> Ty {
    let f = s2n("F");
    let body = pre_rep(&f, t);
    Ty::lam(f, star_to_star(), body)
}

/// Inhabitant of an arbitrary kind. `*` -> `forall a. a`; `k1 -> k2` ->
/// `lam (a : k1). inh(k2)`.
fn inh(k: &Kind) -> Ty {
    let a = s2n("a");
    match k {
        Kind::Star => Ty::forall(a.clone(), Kind::Star, Ty::Var(a)),
        Kind::Arr(k1, k2) => Ty::lam(a, (**k1).clone(), inh(k2)),
    }
}

struct Quoter {
    env: typecheck::Env,
    f: TyName,
    abs: TmName,
    app: TmName,
    tabs: TmName,
    tapp: TmName,
}

/// Encode closed `tm` of source type `ty` into its deep representation.
///
/// The result type-checks against `Exp [[ty]]` in an environment exporting
/// the standard preamble (`Op`, `Strip`, `Abs`, `App`, `TAbs`, `TApp`, `Exp`).
pub fn quote(env: &typecheck::Env, tm: &Tm, ty: &Ty) -> Result<Tm> {
    let mut env = env.clone();
    typecheck::check(&mut env, tm, ty)?;
    // A well-typed term's free names are either type aliases or variables.
    if let Some(n) = tm.fv().iter().find(|n| !env.is_alias(n)) {
        return Err(Error::Type(format!(
            "quote: free variable {n}, only closed terms can be quoted"
        )));
    }
    let ty = nf(&env, ty);
    let mut q = Quoter {
        env,
        f: s2n("F"),
        abs: s2n("abs"),
        app: s2n("app"),
        tabs: s2n("tabs"),
        tapp: s2n("tapp"),
    };
    let inner = q.go(tm, &ty)?;
    let cons = [
        (q.abs, "Abs"),
        (q.app, "App"),
        (q.tabs, "TAbs"),
        (q.tapp, "TApp"),
    ];
    let body = cons.into_iter().rev().fold(inner, |acc, (x, t)| {
        Tm::lam(x, at(&Name::global(t), Ty::Var(q.f.clone())), acc)
    });
    Ok(Tm::tlam(q.f, star_to_star(), body))
}

impl Quoter {
    fn pre(&self, t: &Ty) -> Ty {
        pre_rep(&self.f, t)
    }

    fn infer(&mut self, tm: &Tm) -> Result<Ty> {
        let t = typecheck::infer(&mut self.env, tm)?;
        Ok(nf(&self.env, &t))
    }

    fn go(&mut self, tm: &Tm, ty: &Ty) -> Result<Tm> {
        match tm {
            Tm::Var(_) => Ok(tm.clone()),
            Tm::Lam(b) => {
                let ((x, dom), body) = b.unbind_ref();
                let Ty::Arr(_, cod) = ty else {
                    return Err(Error::Type("quote: lambda needs arrow type".into()));
                };
                let dom = nf(&self.env, &dom);
                self.env.bind_term(&x, dom.clone().into());
                let qbody = self.go(&body, cod)?;
                let (dom, cod) = (self.pre(&dom), self.pre(cod));
                let inner = Tm::lam(x, at(&self.f, dom.clone()), qbody);
                Ok(Tm::app(
                    Tm::tapp(Tm::tapp(Tm::Var(self.abs.clone()), dom), cod),
                    inner,
                ))
            }
            Tm::App(g, x) => {
                let gt = self.infer(g)?;
                let Ty::Arr(dom, cod) = &gt else {
                    return Err(Error::Type("quote: application of non-function".into()));
                };
                let qg = self.go(g, &gt)?;
                let qx = self.go(x, dom)?;
                let (dom, cod) = (self.pre(dom), self.pre(cod));
                Ok(Tm::app(
                    Tm::app(Tm::tapp(Tm::tapp(Tm::Var(self.app.clone()), dom), cod), qg),
                    qx,
                ))
            }
            Tm::TLam(b) => {
                let ((a, k), body) = b.unbind_ref();
                let Ty::Forall(tb) = ty else {
                    return Err(Error::Type("quote: type-lambda needs forall type".into()));
                };
                let body_ty = tb.instantiate(&Ty::Var(a.clone()));
                self.env.bind_tyvar(&a, k.clone());
                let qbody = self.go(&body, &body_ty)?;
                let a_pre = Ty::forall(a.clone(), k.clone(), at(&self.f, self.pre(&body_ty)));
                let strip = self.strip(&a, &k, &body_ty);
                Ok(Tm::app(
                    Tm::app(Tm::tapp(Tm::Var(self.tabs.clone()), a_pre), strip),
                    Tm::tlam(a, k, qbody),
                ))
            }
            Tm::TApp(e, sigma) => {
                let et = self.infer(e)?;
                let Ty::Forall(eb) = &et else {
                    return Err(Error::Type("quote: type-application of non-forall".into()));
                };
                let ((alpha, k), tau) = eb.unbind_ref();
                let qe = self.go(e, &et)?;
                let sigma = nf(&self.env, sigma);
                let tau_pre = self.pre(&tau);
                let b_ty = tau_pre.subst(&alpha, &self.pre(&sigma));
                let a_ty = Ty::forall(alpha.clone(), k.clone(), at(&self.f, tau_pre));
                let inst = self.inst(&alpha, &k, &tau, &sigma);
                Ok(Tm::app(
                    Tm::tapp(
                        Tm::app(Tm::tapp(Tm::Var(self.tapp.clone()), a_ty), qe),
                        b_ty,
                    ),
                    inst,
                ))
            }
            Tm::Int(_) | Tm::Bool(_) | Tm::Let(..) | Tm::If(..) | Tm::Bin(..) | Tm::Ann(..) => {
                Err(Error::Type(
                    "quote: only pure F-omega (var, lam, app, tlam, tapp) is supported".into(),
                ))
            }
        }
    }

    /// The strip function for `/\(alpha : k). body` at `forall alpha:k. tau`,
    /// of type `Strip F (forall alpha:k. F [[tau]])`.
    fn strip(&self, alpha: &TyName, k: &Kind, tau: &Ty) -> Tm {
        let (b, c) = (s2n("b"), s2n("c"));
        let (fun, arg) = (s2n("f"), s2n("x"));
        let inh_k = inh(k);
        let tau_pre = self.pre(tau);
        let gamma = tau_pre.subst(alpha, &inh_k);
        let g_ty = Ty::forall(
            c.clone(),
            Kind::Star,
            Ty::arr(at(&self.f, Ty::Var(c)), Ty::Var(b.clone())),
        );
        let x_ty = Ty::forall(alpha.clone(), k.clone(), at(&self.f, tau_pre));
        let body = Tm::app(
            Tm::tapp(Tm::Var(fun.clone()), gamma),
            Tm::tapp(Tm::Var(arg.clone()), inh_k),
        );
        Tm::tlam(b, Kind::Star, Tm::lam(fun, g_ty, Tm::lam(arg, x_ty, body)))
    }

    /// The inst function for `e [sigma]` where `e : forall alpha:k. tau`, of
    /// type `(forall alpha:k. F [[tau]]) -> F [[tau[sigma/alpha]]]`.
    fn inst(&self, alpha: &TyName, k: &Kind, tau: &Ty, sigma: &Ty) -> Tm {
        let g = s2n("g");
        let g_ty = Ty::forall(alpha.clone(), k.clone(), at(&self.f, self.pre(tau)));
        Tm::lam(g.clone(), g_ty, Tm::tapp(Tm::Var(g), self.pre(sigma)))
    }
}
