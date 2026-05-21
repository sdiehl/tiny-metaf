-- deep self-representation of system f-omega. unlike shallow.f, this one
-- supports many operations: unquote, size, isAbs, isNF, cps, ...
--
-- the pre-representation of a type t is parametric in a type operator F that
-- gets to "interpret" every variable position:
--
--   exp a   = forall F : * -> *. abs F -> app F -> tabs F -> tapp F -> op F a
--   op F a  = F (a F)
--
-- a represented term is a record of four functions (abs, app, tabs, tapp),
-- one per source constructor. each operation we want (size, cps, ...) picks
-- a different F and supplies a matching record.
--
-- the tricky bit is type-abstraction. when you instantiate a represented
-- forall at an arbitrary kind, you need a way to "strip" the kind down to *
-- so it fits the abs/app interface. the Strip type below carries exactly that
-- bridge, parameterised by a kind inhabitant (Bot at kind *, a lambda tower
-- at higher kinds). that's what lets qmid work below at kind (* -> *).

-- --------------------------------------------------------------------------
-- the encoding interface
-- --------------------------------------------------------------------------

type Op    = lam (F : * -> *). lam (a : (* -> *) -> *). F (a F);
type Strip = lam (F : * -> *). lam (a : *).
  forall b. (forall c. F c -> b) -> a -> b;

type Abs  = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (F a -> F b);
type App  = lam (F : * -> *). forall a. forall b. F (F a -> F b) -> F a -> F b;
type TAbs = lam (F : * -> *). forall a. Strip F a -> a -> F a;
type TApp = lam (F : * -> *). forall a. F a -> forall b. (a -> F b) -> F b;

type Exp = lam (a : (* -> *) -> *).
  forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> Op F a;

-- canonical inhabitant of kind *, used by the strip functions.
type Bot = forall a. a;

-- church pair, used by isNF to track (in-normal-form, is-neutral).
type Pair = lam (a : *). lam (b : *). forall r. (a -> b -> r) -> r;

let mkPair : forall a. forall b. a -> b -> Pair a b =
  /\a. /\b. \(x : a). \(y : b). /\r. \(f : a -> b -> r). f x y;

let pfst : forall a. forall b. Pair a b -> a =
  /\a. /\b. \(p : Pair a b). p [a] (\(x : a). \(y : b). x);

let psnd : forall a. forall b. Pair a b -> b =
  /\a. /\b. \(p : Pair a b). p [b] (\(x : a). \(y : b). y);

-- --------------------------------------------------------------------------
-- represented terms
-- --------------------------------------------------------------------------

-- qid encodes /\a. \x. x. the strip just passes Bot as the dummy type.
type QIdPre = lam (F : * -> *). forall a. F (F a -> F a);

let qid : Exp QIdPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tabs [forall a. F (F a -> F a)]
      (/\b. \(f : forall c. F c -> b). \(x : forall a. F (F a -> F a)).
         f [F Bot -> F Bot] (x [Bot]))
      (/\a. abs [a] [a] (\(x : F a). x));

-- qmid encodes /\(M : * -> *). /\a. \(x : M a). x. this is the case that
-- needs the strip machinery: the outer type-abstraction is at kind (* -> *),
-- so its inhabitant is the lambda (lam a. Bot).
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

-- qidLam encodes \(x : Int). x. pure lambda, head is abs.
type QIdLamPre = lam (F : * -> *). F Int -> F Int;

let qidLam : Exp QIdLamPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    abs [Int] [Int] (\(x : F Int). x);

-- qidInt encodes (qid [Int]). the head is tapp.
type QIdIntPre = lam (F : * -> *). F Int -> F Int;

let qidInt : Exp QIdIntPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tapp [forall a. F (F a -> F a)]
         (qid [F] abs app tabs tapp)
         [F Int -> F Int]
         (\(g : forall a. F (F a -> F a)). g [Int]);

-- --------------------------------------------------------------------------
-- operations
-- --------------------------------------------------------------------------

-- unquote (F := Id): recover the original host-language term.
type Id = lam (a : *). a;

let unquote : forall (a : (* -> *) -> *). Exp a -> Op Id a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Id]
      (/\b. /\c. \(f : b -> c). f)
      (/\b. /\c. \(f : b -> c). \(x : b). f x)
      (/\b. \(s : Strip Id b). \(x : b). x)
      (/\b. \(x : b). /\c. \(f : b -> c). f x);

-- size (F := KNat): count ast nodes, all four constructors weight 1.
type KNat = lam (a : *). Int;

let size : forall (a : (* -> *) -> *). Exp a -> Op KNat a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [KNat]
      (/\b. /\c. \(body : Int -> Int). 1 + body 0)
      (/\b. /\c. \(f : Int). \(x : Int). 1 + f + x)
      (/\b. \(s : Strip KNat b). \(x : b).
         1 + s [Int] (/\c. \(n : Int). n) x)
      (/\b. \(x : Int). /\c. \(f : b -> Int). 1 + x);

-- isAbs (F := KBool): true only when the head constructor is abs (a lambda).
type KBool = lam (a : *). Bool;

let isAbs : forall (a : (* -> *) -> *). Exp a -> Op KBool a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [KBool]
      (/\b. /\c. \(body : Bool -> Bool). true)
      (/\b. /\c. \(f : Bool). \(x : Bool). false)
      (/\b. \(s : Strip KBool b). \(x : b). false)
      (/\b. \(x : Bool). /\c. \(f : b -> Bool). false);

-- isNF (F := lam a. Pair Bool Bool): each subterm carries (is_nf, is_neutral).
-- a lambda body is checked by feeding it a fake "variable" Pair true true.
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

-- cps (F := Ct): convert the term to continuation-passing style.
type Ct = lam (a : *). forall r. (a -> r) -> r;

let cps : forall (a : (* -> *) -> *). Exp a -> Op Ct a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Ct]
      -- abs: hand the lambda body to the continuation
      (/\b. /\c. \(body : Ct b -> Ct c).
        /\g. \(k : (Ct b -> Ct c) -> g). k body)
      -- app: evaluate f, get the function, apply, then continue
      (/\b. /\c. \(f : Ct (Ct b -> Ct c)). \(x : Ct b).
        /\g. \(k : c -> g).
          f [g] (\(fn : Ct b -> Ct c). fn x [g] k))
      -- tabs: a type-abstraction value, hand it to the continuation
      (/\b. \(s : Strip Ct b). \(x : b).
        /\g. \(k : b -> g). k x)
      -- tapp: evaluate, instantiate, continue
      (/\b. \(e_ct : Ct b). /\c. \(inst : b -> Ct c).
        /\g. \(k : c -> g).
          e_ct [g] (\(v : b). inst v [g] k));

-- --------------------------------------------------------------------------
-- demo runs
-- --------------------------------------------------------------------------

-- unquote: round-trip the represented terms back into runnable functions.
eval (unquote [QIdPre] qid) [Int] 42;
eval (unquote [QMIdPre] qmid) [Id] [Int] 99;
eval (unquote [QIdLamPre] qidLam) 7;
eval (unquote [QIdIntPre] qidInt) 5;

-- size: total ast nodes.
eval size [QIdPre] qid;
eval size [QMIdPre] qmid;
eval size [QIdLamPre] qidLam;
eval size [QIdIntPre] qidInt;

-- isAbs: only qidLam is a bare lambda.
eval isAbs [QIdPre] qid;
eval isAbs [QIdLamPre] qidLam;
eval isAbs [QIdIntPre] qidInt;

-- isNF: project the first component of the pair.
eval pfst [Bool] [Bool] (isNF [QIdPre] qid);
eval pfst [Bool] [Bool] (isNF [QMIdPre] qmid);
eval pfst [Bool] [Bool] (isNF [QIdLamPre] qidLam);
eval pfst [Bool] [Bool] (isNF [QIdIntPre] qidInt);

-- cps: feed a trivial constant continuation.
eval (cps [QIdPre] qid) [Int]
  (\(f : forall a. Ct (Ct a -> Ct a)). 1234);
