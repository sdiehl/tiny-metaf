//! Full beta-normalisation of pure F-omega terms and their type annotations.
//!
//! Terminates on well-typed pure terms (strong normalisation); anything
//! outside the pure fragment is left untouched.

use crate::syntax::{Tm, Ty};
use crate::typecheck::{nf, Env};

#[must_use]
pub fn norm(env: &Env, tm: &Tm) -> Tm {
    match tm {
        Tm::Lam(b) => {
            let ((x, t), body) = b.unbind_ref();
            Tm::lam(x, nf(env, &t), norm(env, &body))
        }
        Tm::TLam(b) => {
            let ((a, k), body) = b.unbind_ref();
            Tm::tlam(a, k, norm(env, &body))
        }
        Tm::App(f, x) => match norm(env, f) {
            Tm::Lam(b) => norm(env, &b.instantiate::<Tm>(x)),
            f => Tm::app(f, norm(env, x)),
        },
        Tm::TApp(f, t) => match norm(env, f) {
            Tm::TLam(b) => norm(env, &b.instantiate::<Ty>(t)),
            f => Tm::tapp(f, nf(env, t)),
        },
        _ => tm.clone(),
    }
}

/// No beta-redex anywhere, the property Brown & Palsberg demand of a quoter.
#[must_use]
pub fn is_normal(tm: &Tm) -> bool {
    match tm {
        Tm::Lam(b) => is_normal(&b.unbind_ref().1),
        Tm::TLam(b) => is_normal(&b.unbind_ref().1),
        Tm::App(f, x) => !matches!(**f, Tm::Lam(_)) && is_normal(f) && is_normal(x),
        Tm::TApp(f, _) => !matches!(**f, Tm::TLam(_)) && is_normal(f),
        _ => true,
    }
}
