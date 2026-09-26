use tiny_fself::driver::Session;
use tiny_fself::eval::Value;
use tiny_fself::parse;
use tiny_fself::pretty;
use tiny_fself::quote;
use tiny_fself::syntax::{ty_name, Tm, Ty};
use tiny_fself::typecheck;
use unbound::prelude::*;

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
    Ty::app(Ty::Var(ty_name("Exp")), pre_univ)
}

/// Quote `tm : ty`, check the result against `Exp [[ty]]`, and return it.
fn quoted(s: &mut Session, tm: &str, ty: &str) -> (Tm, Ty) {
    let tm = parse::parse_expr(tm).expect("term parses");
    let ty = parse::parse_type(ty).expect("type parses");
    let qtm = quote::quote(&s.tenv, &tm, &ty).expect("quote");
    let univ = quote::pre_rep_universe(&ty);
    typecheck::check(&mut s.tenv, &qtm, &exp_ty(univ.clone())).expect("type-checks");
    (qtm, univ)
}

/// Quote, then evaluate `unquote [[[ty]]] q` followed by `tail`.
fn round_trip(tm: &str, ty: &str, tail: &str) -> Value {
    let mut s = loaded();
    let (qtm, univ) = quoted(&mut s, tm, ty);
    let src = format!(
        "unquote [{}] ({}) {tail}",
        pretty::ty(&univ),
        pretty::tm(&qtm)
    );
    let e = parse::parse_expr(&src).expect("reparses");
    s.eval_expr(&e.into()).expect("eval").1
}

fn int(v: &Value) -> i64 {
    match v {
        Value::Int(i) => *i,
        v => panic!("expected int, got {}", pretty::value(v)),
    }
}

#[test]
fn polymorphic_identity_round_trips() {
    let v = round_trip(r"/\a. \(x : a). x", "forall a. a -> a", "[Int] 42");
    assert_eq!(int(&v), 42);
}

#[test]
fn pure_lambda_round_trips() {
    assert_eq!(int(&round_trip(r"\(x : Int). x", "Int -> Int", "7")), 7);
}

#[test]
fn tapp_round_trips() {
    let v = round_trip(r"(/\a. \(x : a). x) [Int]", "Int -> Int", "123");
    assert_eq!(int(&v), 123);
}

#[test]
fn nested_type_binders_do_not_capture() {
    let v = round_trip(
        r"/\b. /\a. \(x : b). x",
        "forall b. forall a. b -> b",
        "[Int] [Bool] 5",
    );
    assert_eq!(int(&v), 5);
}

#[test]
fn binders_named_like_constructors_do_not_capture() {
    let v = round_trip(r"\(abs : Int). \(y : Int). y", "Int -> Int -> Int", "1 2");
    assert_eq!(int(&v), 2);
}

#[test]
fn type_variable_named_f_does_not_capture() {
    let v = round_trip(r"/\F. \(x : F). x", "forall F. F -> F", "[Int] 9");
    assert_eq!(int(&v), 9);
}

#[test]
fn pretty_printed_quote_reparses() {
    let mut s = loaded();
    let ty = "forall b. forall a. b -> a -> b";
    let (qtm, univ) = quoted(&mut s, r"/\b. /\a. \(x : b). \(y : a). x", ty);
    let reparsed = parse::parse_expr(&pretty::tm(&qtm)).expect("reparse");
    assert!(reparsed.aeq(&qtm));
    typecheck::check(&mut s.tenv, &reparsed, &exp_ty(univ)).expect("ok");
}

#[test]
fn literal_is_rejected() {
    let s = loaded();
    assert!(quote::quote(&s.tenv, &Tm::Int(5), &Ty::Int).is_err());
}

#[test]
fn free_variable_is_rejected() {
    let s = loaded();
    let tm = parse::parse_expr("unquote").unwrap();
    let ty = parse::parse_type("forall (a : (* -> *) -> *). Exp a -> Op Id a").unwrap();
    let err = quote::quote(&s.tenv, &tm, &ty).unwrap_err().to_string();
    assert!(err.contains("free variable"), "{err}");
}
