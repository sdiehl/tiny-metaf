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

-- Bot inhabits kind *. Used as the kind-* inhabitant in strip functions.
type Bot = forall a. a;

-- ---------- qid : representation of (/\a. \(x:a). x) at type forall a. a -> a
-- Pre-rep:  lam F. forall a. F (F a -> F a)

type QIdPre = lam (F : * -> *). forall a. F (F a -> F a);

let qid : Exp QIdPre =
  /\(F : * -> *). \(abs : Abs F). \(app : App F). \(tabs : TAbs F). \(tapp : TApp F).
    tabs [forall a. F (F a -> F a)]
      (/\b. \(f : forall c. F c -> b). \(x : forall a. F (F a -> F a)).
         f [F Bot -> F Bot] (x [Bot]))
      (/\a. abs [a] [a] (\(x : F a). x));

-- ---------- qmid : representation of (/\(M : * -> *). /\a. \(x : M a). x)
-- This is BEYOND System F: M is a type abstraction at kind (* -> *).
-- Strip handles it without any kind polymorphism in the host language.
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

-- ---------- unquote : F := Identity. Recovers the host term.

type Id = lam (a : *). a;

let unquote : forall (a : (* -> *) -> *). Exp a -> Op Id a =
  /\(a : (* -> *) -> *). \(e : Exp a).
    e [Id]
      (/\b. /\c. \(f : b -> c). f)
      (/\b. /\c. \(f : b -> c). \(x : b). f x)
      (/\b. \(s : Strip Id b). \(x : b). x)
      (/\b. \(x : b). /\c. \(f : b -> c). f x);

-- ---------- evaluations

-- Plain System F: identity at Int.
eval (unquote [QIdPre] qid) [Int] 42;

-- F-omega: identity through a kind-(* -> *) abstraction, then a kind-* one.
eval (unquote [QMIdPre] qmid) [Id] [Int] 99;
