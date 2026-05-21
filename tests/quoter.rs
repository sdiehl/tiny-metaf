use std::rc::Rc;

use tiny_fself::driver::Session;
use tiny_fself::eval::Value;
use tiny_fself::parse;
use tiny_fself::pretty;
use tiny_fself::quote;
use tiny_fself::syntax::{name, Kind, Tm, Ty};
use tiny_fself::typecheck;

const PREAMBLE: &str = r"
type Op    = lam (F : * -> *). lam (a : (* -> *) -> *). F (a F);
type Strip = lam (F : * -> *). lam (a : *).
  forall b. (forall c. F c -> b) -> a -> b;
type Abs  = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (F a -> F b);
type App  = lam (F : * -> *). forall a. forall b. F (F a -> F b) -> F a -> F b;
type TAbs = lam (F : * -> *). forall a. Strip F a -> a -> F a;
type TApp = lam (F : * -> *). forall a. F a -> forall b. (a -> F b) -> F b;
type Exp = lam (a : (* -> *) -> *).
  forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> Op F a;
type Id = lam (a : *). a;
let unquote : forall (a : (* -> *) -> *). Exp a -> Op Id a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Id]
      (/\b. /\c. \(f : b -> c). f)
      (/\b. /\c. \(f : b -> c). \(x : b). f x)
      (/\b. \(s : Strip Id b). \(x : b). x)
      (/\b. \(x : b). /\c. \(f : b -> c). f x);
";

fn loaded() -> Session {
    let prog = parse::parse_program(PREAMBLE).expect("preamble parses");
    let mut s = Session::new();
    s.process_program(&prog).expect("preamble checks");
    s
}

fn exp_ty(pre_univ: Ty) -> Ty {
    Ty::App(Rc::new(Ty::Var(name("Exp"))), Rc::new(pre_univ))
}

/// Quote, type-check against `Exp [[ty]]`, then evaluate
/// `unquote [pre_rep_universe(ty)] qtm <tail-applied to extra args>`.
fn round_trip(tm: &Tm, ty: &Ty, tail: &[Either]) -> Value {
    let mut s = loaded();
    let qtm = quote::quote(&s.tenv, tm, ty).expect("quote");
    let expected = exp_ty(quote::pre_rep_universe(ty));
    typecheck::check(&mut s.tenv, &qtm, &expected).expect("type-checks");
    let unq = Tm::TApp(
        Rc::new(Tm::Var(name("unquote"))),
        Rc::new(quote::pre_rep_universe(ty)),
    );
    let mut e = Tm::App(Rc::new(unq), Rc::new(qtm));
    for step in tail {
        e = match step {
            Either::T(t) => Tm::TApp(Rc::new(e), Rc::new(t.clone())),
            Either::V(v) => Tm::App(Rc::new(e), Rc::new(v.clone())),
        };
    }
    let (_t, v) = s.eval_expr(&Rc::new(e)).expect("eval");
    v
}

enum Either {
    T(Ty),
    V(Tm),
}

#[test]
fn polymorphic_identity_round_trips() {
    let id = Tm::TLam(
        name("a"),
        Rc::new(Kind::Star),
        Rc::new(Tm::Lam(
            name("x"),
            Rc::new(Ty::Var(name("a"))),
            Rc::new(Tm::Var(name("x"))),
        )),
    );
    let ty = Ty::Forall(
        name("a"),
        Rc::new(Kind::Star),
        Rc::new(Ty::Arr(
            Rc::new(Ty::Var(name("a"))),
            Rc::new(Ty::Var(name("a"))),
        )),
    );
    let v = round_trip(&id, &ty, &[Either::T(Ty::Int), Either::V(Tm::Int(42))]);
    assert!(matches!(v, Value::Int(42)), "got {}", pretty::value(&v));
}

#[test]
fn pure_lambda_round_trips() {
    let lam = Tm::Lam(name("x"), Rc::new(Ty::Int), Rc::new(Tm::Var(name("x"))));
    let ty = Ty::Arr(Rc::new(Ty::Int), Rc::new(Ty::Int));
    let v = round_trip(&lam, &ty, &[Either::V(Tm::Int(7))]);
    assert!(matches!(v, Value::Int(7)), "got {}", pretty::value(&v));
}

#[test]
fn tapp_round_trips() {
    // (qid [Int]) at Int -> Int
    let qid = Tm::TLam(
        name("a"),
        Rc::new(Kind::Star),
        Rc::new(Tm::Lam(
            name("x"),
            Rc::new(Ty::Var(name("a"))),
            Rc::new(Tm::Var(name("x"))),
        )),
    );
    let qid_int = Tm::TApp(Rc::new(qid), Rc::new(Ty::Int));
    let ty = Ty::Arr(Rc::new(Ty::Int), Rc::new(Ty::Int));
    let v = round_trip(&qid_int, &ty, &[Either::V(Tm::Int(123))]);
    assert!(matches!(v, Value::Int(123)), "got {}", pretty::value(&v));
}

#[test]
fn pretty_printed_quote_reparses() {
    let id = Tm::TLam(
        name("a"),
        Rc::new(Kind::Star),
        Rc::new(Tm::Lam(
            name("x"),
            Rc::new(Ty::Var(name("a"))),
            Rc::new(Tm::Var(name("x"))),
        )),
    );
    let ty = Ty::Forall(
        name("a"),
        Rc::new(Kind::Star),
        Rc::new(Ty::Arr(
            Rc::new(Ty::Var(name("a"))),
            Rc::new(Ty::Var(name("a"))),
        )),
    );
    let mut s = loaded();
    let qtm = quote::quote(&s.tenv, &id, &ty).expect("quote");
    let reparsed = parse::parse_expr(&pretty::tm(&qtm)).expect("reparse");
    typecheck::check(
        &mut s.tenv,
        &reparsed,
        &exp_ty(quote::pre_rep_universe(&ty)),
    )
    .expect("ok");
}

#[test]
fn literal_is_rejected() {
    let s = loaded();
    assert!(quote::quote(&s.tenv, &Tm::Int(5), &Ty::Int).is_err());
}
