use std::fmt;
use std::rc::Rc;

pub type Name = Rc<str>;

#[must_use]
pub fn name(s: &str) -> Name {
    Rc::from(s)
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Var(Name),
    Arr(Rc<Self>, Rc<Self>),
    Forall(Name, Rc<Kind>, Rc<Self>),
    Lam(Name, Rc<Kind>, Rc<Self>),
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
    pub fn forall(a: &str, b: Self) -> Self {
        Self::Forall(name(a), Rc::new(Kind::Star), Rc::new(b))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Debug, Clone)]
pub enum Tm {
    Var(Name),
    Int(i64),
    Bool(bool),
    Lam(Name, Rc<Ty>, Rc<Self>),
    App(Rc<Self>, Rc<Self>),
    TLam(Name, Rc<Kind>, Rc<Self>),
    TApp(Rc<Self>, Rc<Ty>),
    Let(Name, Option<Rc<Ty>>, Rc<Self>, Rc<Self>),
    If(Rc<Self>, Rc<Self>, Rc<Self>),
    Bin(BinOp, Rc<Self>, Rc<Self>),
    Fix(Name, Rc<Ty>, Rc<Self>),
    Ann(Rc<Self>, Rc<Ty>),
}

#[derive(Debug, Clone)]
pub enum Decl {
    TypeAlias(Name, Rc<Ty>),
    Let(Name, Rc<Ty>, Rc<Tm>),
    Eval(Rc<Tm>),
}

#[derive(Debug, Clone)]
pub enum ReplItem {
    Decl(Decl),
    Expr(Rc<Tm>),
}

#[must_use]
pub fn fold_lams(params: Vec<(Name, Rc<Ty>)>, body: Tm) -> Tm {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (nm, ty)| Tm::Lam(nm, ty, Rc::new(acc)))
}

#[must_use]
pub fn fold_tlams(params: Vec<(Name, Rc<Kind>)>, body: Tm) -> Tm {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (nm, k)| Tm::TLam(nm, k, Rc::new(acc)))
}

#[must_use]
pub fn fold_foralls(params: Vec<(Name, Rc<Kind>)>, body: Ty) -> Ty {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (nm, k)| Ty::Forall(nm, k, Rc::new(acc)))
}

#[must_use]
pub fn fold_tylams(params: Vec<(Name, Rc<Kind>)>, body: Ty) -> Ty {
    params
        .into_iter()
        .rev()
        .fold(body, |acc, (nm, k)| Ty::Lam(nm, k, Rc::new(acc)))
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
