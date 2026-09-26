use std::fmt;
use std::rc::Rc;

use unbound::prelude::*;

pub type TyName = Name<Ty>;
pub type TmName = Name<Tm>;

#[derive(Debug, Clone, PartialEq, Eq, Alpha, Subst)]
#[subst(_)]
pub enum Kind {
    Star,
    Arr(Rc<Self>, Rc<Self>),
}

impl Kind {
    #[must_use]
    pub fn arr(a: Self, b: Self) -> Self {
        Self::Arr(Rc::new(a), Rc::new(b))
    }
}

pub type TyBind = Bind<(TyName, Kind), Rc<Ty>>;

#[derive(Debug, Clone, Alpha, Subst)]
#[subst(Self, Tm)]
pub enum Ty {
    Var(TyName),
    Arr(Rc<Self>, Rc<Self>),
    Forall(TyBind),
    Lam(TyBind),
    App(Rc<Self>, Rc<Self>),
    Int,
    Bool,
}

impl Ty {
    #[must_use]
    pub fn arr(a: Self, b: Self) -> Self {
        Self::Arr(Rc::new(a), Rc::new(b))
    }

    #[must_use]
    pub fn app(f: Self, x: Self) -> Self {
        Self::App(Rc::new(f), Rc::new(x))
    }

    #[must_use]
    pub fn forall(a: TyName, k: Kind, body: Self) -> Self {
        Self::Forall(Bind::new((a, k), Rc::new(body)))
    }

    #[must_use]
    pub fn lam(a: TyName, k: Kind, body: Self) -> Self {
        Self::Lam(Bind::new((a, k), Rc::new(body)))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Alpha, Subst)]
#[subst(_)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Eq,
    Lt,
    And,
    Or,
}

impl BinOp {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Eq => "==",
            Self::Lt => "<",
            Self::And => "&&",
            Self::Or => "||",
        }
    }
}

#[derive(Debug, Clone, Alpha, Subst)]
#[subst(Self, Ty)]
pub enum Tm {
    Var(TmName),
    Int(i64),
    Bool(bool),
    Lam(Bind<(TmName, Rc<Ty>), Rc<Self>>),
    App(Rc<Self>, Rc<Self>),
    TLam(Bind<(TyName, Kind), Rc<Self>>),
    TApp(Rc<Self>, Rc<Ty>),
    Let(Rc<Self>, Bind<(TmName, Option<Rc<Ty>>), Rc<Self>>),
    If(Rc<Self>, Rc<Self>, Rc<Self>),
    Bin(BinOp, Rc<Self>, Rc<Self>),
    Ann(Rc<Self>, Rc<Ty>),
}

impl Tm {
    #[must_use]
    pub fn lam(x: TmName, ty: Ty, body: Self) -> Self {
        Self::Lam(Bind::new((x, Rc::new(ty)), Rc::new(body)))
    }

    #[must_use]
    pub fn tlam(a: TyName, k: Kind, body: Self) -> Self {
        Self::TLam(Bind::new((a, k), Rc::new(body)))
    }

    #[must_use]
    pub fn app(f: Self, x: Self) -> Self {
        Self::App(Rc::new(f), Rc::new(x))
    }

    #[must_use]
    pub fn tapp(f: Self, t: Ty) -> Self {
        Self::TApp(Rc::new(f), Rc::new(t))
    }

    #[must_use]
    pub fn let_(x: TmName, ann: Option<Ty>, v: Self, body: Self) -> Self {
        Self::Let(Rc::new(v), Bind::new((x, ann.map(Rc::new)), Rc::new(body)))
    }
}

#[derive(Debug, Clone)]
pub enum Decl {
    TypeAlias(TyName, Rc<Ty>),
    Let(TmName, Rc<Ty>, Rc<Tm>),
    Eval(Rc<Tm>),
}

#[derive(Debug, Clone)]
pub enum ReplItem {
    Decl(Decl),
    Expr(Rc<Tm>),
}

#[must_use]
pub fn fold_lams(params: Vec<(TmName, Ty)>, body: Tm) -> Tm {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (x, ty)| Tm::lam(x, ty, acc))
}

#[must_use]
pub fn fold_tlams(params: Vec<(TyName, Kind)>, body: Tm) -> Tm {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (a, k)| Tm::tlam(a, k, acc))
}

#[must_use]
pub fn fold_foralls(params: Vec<(TyName, Kind)>, body: Ty) -> Ty {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (a, k)| Ty::forall(a, k, acc))
}

#[must_use]
pub fn fold_tylams(params: Vec<(TyName, Kind)>, body: Ty) -> Ty {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (a, k)| Ty::lam(a, k, acc))
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
