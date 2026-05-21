-- Brown & Palsberg, POPL 2016 (Figure 3): paper-accurate deep self-representation
-- of System F-omega. Extensional encoding with Strip instantiation functions, so
-- type abstractions at any kind go through without kind polymorphism.
--
--   U      = (* -> *) -> *                                 (kind of pre-reps)
--   Op   F a = F (a F)                                     (interp under F)
--   Strip F a = forall b. (forall c. F c -> b) -> a -> b   (kind-stripping)
--   Abs  F = forall a b. (F a -> F b) -> F (F a -> F b)
--   App  F = forall a b. F (F a -> F b) -> F a -> F b
--   TAbs F = forall a. Strip F a -> a -> F a
--   TApp F = forall a. F a -> forall b. (a -> F b) -> F b
--   Exp  a = forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> Op F a

-- ---------- kind and type definitions ------------------------------------
-- The kind U = (* -> *) -> * is inlined; our language has no kind aliases.

type Op    = lam (F : * -> *). lam (a : (* -> *) -> *). F (a F);
type Strip = lam (F : * -> *). lam (a : *).
  forall b. (forall c. F c -> b) -> a -> b;

type Abs  = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (F a -> F b);
type App  = lam (F : * -> *). forall a. forall b. F (F a -> F b) -> F a -> F b;
type TAbs = lam (F : * -> *). forall a. Strip F a -> a -> F a;
type TApp = lam (F : * -> *). forall a. F a -> forall b. (a -> F b) -> F b;

type Exp = lam (a : (* -> *) -> *).
  forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> Op F a;

-- Bot inhabits kind *; used as the kind-* inhabitant in strip functions.
type Bot = forall a. a;

-- ---------- Church pair (for isNF interpretation) ------------------------

type Pair = lam (a : *). lam (b : *). forall r. (a -> b -> r) -> r;

let mkPair : forall a. forall b. a -> b -> Pair a b =
  /\a. /\b. \(x : a). \(y : b). /\r. \(f : a -> b -> r). f x y;

let pfst : forall a. forall b. Pair a b -> a =
  /\a. /\b. \(p : Pair a b). p [a] (\(x : a). \(y : b). x);

let psnd : forall a. forall b. Pair a b -> b =
  /\a. /\b. \(p : Pair a b). p [b] (\(x : a). \(y : b). y);

-- =====================================================================
-- Represented terms
-- =====================================================================

-- qid : (/\a. \(x:a). x) at type forall a. a -> a
-- Pre-rep:  lam F. forall a. F (F a -> F a)

type QIdPre = lam (F : * -> *). forall a. F (F a -> F a);

let qid : Exp QIdPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tabs [forall a. F (F a -> F a)]
      (/\b. \(f : forall c. F c -> b). \(x : forall a. F (F a -> F a)).
         f [F Bot -> F Bot] (x [Bot]))
      (/\a. abs [a] [a] (\(x : F a). x));

-- qmid : (/\(M : * -> *). /\a. \(x : M a). x)
-- BEYOND System F: M is a type abstraction at kind (* -> *).
-- Strip handles this with the (* -> *) inhabitant (lam a. Bot).
-- Pre-rep:  lam F. forall (M : * -> *). F (forall a. F (F (M a) -> F (M a)))

type QMIdPre = lam (F : * -> *).
  forall (M : * -> *). F (forall a. F (F (M a) -> F (M a)));

let qmid : Exp QMIdPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tabs [forall (M : * -> *). F (forall a. F (F (M a) -> F (M a)))]
      (/\b. \(f : forall c. F c -> b).
            \(x : forall (M : * -> *). F (forall a. F (F (M a) -> F (M a)))).
         f [forall a. F (F Bot -> F Bot)] (x [lam (a : *). Bot]))
      (/\(M : * -> *).
        tabs [forall a. F (F (M a) -> F (M a))]
          (/\b. \(f : forall c. F c -> b). \(x : forall a. F (F (M a) -> F (M a))).
             f [F (M Bot) -> F (M Bot)] (x [Bot]))
          (/\a. abs [M a] [M a] (\(x : F (M a)). x)));

-- qidLam : (\(x : Int). x) at type Int -> Int. A pure lambda; head is abs.
-- Pre-rep:  lam F. F Int -> F Int

type QIdLamPre = lam (F : * -> *). F Int -> F Int;

let qidLam : Exp QIdLamPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    abs [Int] [Int] (\(x : F Int). x);

-- qidInt : (qid [Int]) at type Int -> Int. Exercises the tapp constructor.
-- Pre-rep:  lam F. F Int -> F Int

type QIdIntPre = lam (F : * -> *). F Int -> F Int;

let qidInt : Exp QIdIntPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tapp [forall a. F (F a -> F a)]
         (qid [F] abs app tabs tapp)
         [F Int -> F Int]
         (\(g : forall a. F (F a -> F a)). g [Int]);

-- =====================================================================
-- Five operations from Section 7. All have type
--   forall (a : U). Exp a -> Op R a    where R is chosen per operation.
-- =====================================================================

-- ---------- unquote : F := Id. Recovers the host term.

type Id = lam (a : *). a;

let unquote : forall (a : (* -> *) -> *). Exp a -> Op Id a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Id]
      (/\b. /\c. \(f : b -> c). f)
      (/\b. /\c. \(f : b -> c). \(x : b). f x)
      (/\b. \(s : Strip Id b). \(x : b). x)
      (/\b. \(x : b). /\c. \(f : b -> c). f x);

-- ---------- size : F := KNat. Counts AST nodes.

type KNat = lam (a : *). Int;

let size : forall (a : (* -> *) -> *). Exp a -> Op KNat a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [KNat]
      (/\b. /\c. \(body : Int -> Int). 1 + body 0)
      (/\b. /\c. \(f : Int). \(x : Int). 1 + f + x)
      (/\b. \(s : Strip KNat b). \(x : b).
         1 + s [Int] (/\c. \(n : Int). n) x)
      (/\b. \(x : Int). /\c. \(f : b -> Int). 1 + x);

-- ---------- isAbs : F := KBool. True iff top-level constructor is abs.

type KBool = lam (a : *). Bool;

let isAbs : forall (a : (* -> *) -> *). Exp a -> Op KBool a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [KBool]
      (/\b. /\c. \(body : Bool -> Bool). true)
      (/\b. /\c. \(f : Bool). \(x : Bool). false)
      (/\b. \(s : Strip KBool b). \(x : b). false)
      (/\b. \(x : Bool). /\c. \(f : b -> Bool). false);

-- ---------- isNF : F := lam a. Pair Bool Bool.
-- First component: this subterm is in normal form.
-- Second component: this subterm is neutral (head is var, app of neutral, or
-- type-app of neutral). A lambda body is checked by feeding a "variable"
-- (Pair true true).

type PB = lam (a : *). Pair Bool Bool;

let isNF : forall (a : (* -> *) -> *). Exp a -> Op PB a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [PB]
      (/\b. /\c. \(body : Pair Bool Bool -> Pair Bool Bool).
        mkPair [Bool] [Bool]
          (pfst [Bool] [Bool] (body (mkPair [Bool] [Bool] true true)))
          false)
      (/\b. /\c. \(f : Pair Bool Bool). \(x : Pair Bool Bool).
        let nf : Bool =
          psnd [Bool] [Bool] f && pfst [Bool] [Bool] x in
        mkPair [Bool] [Bool] nf nf)
      (/\b. \(s : Strip PB b). \(x : b).
        let bodyP : Pair Bool Bool =
          s [Pair Bool Bool] (/\c. \(p : Pair Bool Bool). p) x in
        mkPair [Bool] [Bool] (pfst [Bool] [Bool] bodyP) false)
      (/\b. \(x : Pair Bool Bool). /\c. \(f : b -> Pair Bool Bool).
        mkPair [Bool] [Bool]
          (psnd [Bool] [Bool] x)
          (psnd [Bool] [Bool] x));

-- ---------- cps : F := Ct (continuation type). CPS-transforms the term.

type Ct = lam (a : *). forall r. (a -> r) -> r;

let cps : forall (a : (* -> *) -> *). Exp a -> Op Ct a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Ct]
      -- Abs Ct: a lambda value, wrapped in a continuation.
      (/\b. /\c. \(body : Ct b -> Ct c).
        /\g. \(k : (Ct b -> Ct c) -> g). k body)
      -- App Ct: evaluate f, get function; apply to x; then continue.
      (/\b. /\c. \(f : Ct (Ct b -> Ct c)). \(x : Ct b).
        /\g. \(k : c -> g).
          f [g] (\(fn : Ct b -> Ct c). fn x [g] k))
      -- TAbs Ct: a type-abstraction value, wrapped in a continuation.
      (/\b. \(s : Strip Ct b). \(x : b).
        /\g. \(k : b -> g). k x)
      -- TApp Ct: evaluate e, instantiate, then continue.
      (/\b. \(e_ct : Ct b). /\c. \(inst : b -> Ct c).
        /\g. \(k : c -> g).
          e_ct [g] (\(v : b). inst v [g] k));

-- =====================================================================
-- Evaluations
-- =====================================================================

-- unquote: round-trip the represented terms back into runnable functions.
eval (unquote [QIdPre] qid) [Int] 42;
eval (unquote [QMIdPre] qmid) [Id] [Int] 99;
eval (unquote [QIdLamPre] qidLam) 7;
eval (unquote [QIdIntPre] qidInt) 5;

-- size: AST node counts.
eval size [QIdPre] qid;
eval size [QMIdPre] qmid;
eval size [QIdLamPre] qidLam;
eval size [QIdIntPre] qidInt;

-- isAbs: true only for lambdas. qidLam is the only one whose head is abs.
eval isAbs [QIdPre] qid;
eval isAbs [QIdLamPre] qidLam;
eval isAbs [QIdIntPre] qidInt;

-- isNF: extract the first component of the Pair.
eval pfst [Bool] [Bool] (isNF [QIdPre] qid);
eval pfst [Bool] [Bool] (isNF [QMIdPre] qmid);
eval pfst [Bool] [Bool] (isNF [QIdLamPre] qidLam);
eval pfst [Bool] [Bool] (isNF [QIdIntPre] qidInt);

-- cps: drive with a trivial continuation that returns a constant.
eval (cps [QIdPre] qid) [Int]
  (\(f : forall a. Ct (Ct a -> Ct a)). 1234);
