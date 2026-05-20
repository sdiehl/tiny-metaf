-- Brown & Palsberg, Section 5: the DEEP self-representation, extended to
-- System F (the represented language has Λ and type application, not just
-- value abstraction). One representation, four interpretations chosen by
-- varying F : * -> *.
--
--   Abs  F = forall a b. (F a -> F b) -> F (a -> b)
--   App  F = forall a b. F (a -> b) -> F a -> F b
--   TAbs F = forall (B : * -> *). (forall a. F (B a)) -> F (forall a. B a)
--   TApp F = forall (B : * -> *). forall a. F (forall c. B c) -> F (B a)
--   Exp a  = forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> F a

-- ---------- type constructors --------------------------------------------

type Id = lam a. a;
type K = lam (a : *). lam (b : *). a;

-- ---------- Church pair (for the isNF interpretation) --------------------

type Pair = lam a. lam b. forall r. (a -> b -> r) -> r;

let mkPair : forall a. forall b. a -> b -> Pair a b =
  /\a. /\b. \(x : a). \(y : b). /\r. \(f : a -> b -> r). f x y;

let fst : forall a. forall b. Pair a b -> a =
  /\a. /\b. \(p : Pair a b). p [a] (\(x : a). \(_y : b). x);

let snd : forall a. forall b. Pair a b -> b =
  /\a. /\b. \(p : Pair a b). p [b] (\(_x : a). \(y : b). y);

-- ---------- the deep encoding -------------------------------------------

type Abs  = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (a -> b);
type App  = lam (F : * -> *). forall a. forall b. F (a -> b) -> F a -> F b;
type TAbs = lam (F : * -> *). forall (B : * -> *). (forall a. F (B a)) -> F (forall a. B a);
type TApp = lam (F : * -> *). forall (B : * -> *). forall a. F (forall c. B c) -> F (B a);
type Exp  = lam a. forall (F : * -> *). Abs F -> App F -> TAbs F -> TApp F -> F a;

-- ---------- represented terms -------------------------------------------

-- qid : \(x : Int). x  at type Int -> Int
let qid : Exp (Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(_tab : TAbs F). \(_tap : TApp F).
    ab [Int] [Int] (\(x : F Int). x);

-- qself : \(x : Int -> Int). x
let qself : Exp ((Int -> Int) -> Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(_tab : TAbs F). \(_tap : TApp F).
    ab [Int -> Int] [Int -> Int] (\(x : F (Int -> Int)). x);

-- qconst : \x y. x
let qconst : Exp (Int -> Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(_tab : TAbs F). \(_tap : TApp F).
    ab [Int] [Int -> Int] (\(x : F Int).
      ab [Int] [Int] (\(_y : F Int). x));

-- qapply : \f x. f x  (NF, one App with neutral head)
let qapply : Exp ((Int -> Int) -> Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(ap : App F). \(_tab : TAbs F). \(_tap : TApp F).
    ab [Int -> Int] [Int -> Int] (\(f : F (Int -> Int)).
      ab [Int] [Int] (\(x : F Int).
        ap [Int] [Int] f x));

-- qredex : (\f. f) (\x. x)  (value-level beta-redex, NOT in NF)
let qredex : Exp (Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(ap : App F). \(_tab : TAbs F). \(_tap : TApp F).
    ap [Int -> Int] [Int -> Int]
      (ab [Int -> Int] [Int -> Int] (\(f : F (Int -> Int)). f))
      (ab [Int] [Int] (\(x : F Int). x));

-- qpolyId : /\a. \(x : a). x  at type forall a. a -> a
let qpolyId : Exp (forall a. a -> a) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(tab : TAbs F). \(_tap : TApp F).
    tab [lam a. a -> a]
      (/\a. ab [a] [a] (\(x : F a). x));

-- qpolyConst : /\a. /\b. \x. \y. x  at type forall a. forall b. a -> b -> a
let qpolyConst : Exp (forall a. forall b. a -> b -> a) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(tab : TAbs F). \(_tap : TApp F).
    tab [lam a. forall b. a -> b -> a]
      (/\a. tab [lam b. a -> b -> a]
        (/\b. ab [a] [b -> a]
          (\(x : F a). ab [b] [a]
            (\(_y : F b). x))));

-- qtyRedex : (/\a. \(x : a). x) [Int]  at type Int -> Int (type-level beta-redex)
let qtyRedex : Exp (Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F). \(tab : TAbs F). \(tap : TApp F).
    tap [lam a. a -> a] [Int]
      (tab [lam a. a -> a]
        (/\a. ab [a] [a] (\(x : F a). x)));

-- ---------- operation 1: unquote (F = Id) --------------------------------

let unquote : forall a. Exp a -> a =
  /\a. \(e : Exp a).
    e [Id]
      (/\a. /\b. \(f : a -> b). f)
      (/\a. /\b. \(f : a -> b). \(x : a). f x)
      (/\(B : * -> *). \(f : forall a. B a). f)
      (/\(B : * -> *). /\a. \(f : forall c. B c). f [a]);

eval unquote [Int -> Int] qid 7;
eval unquote [(Int -> Int) -> Int -> Int] qself (\(x : Int). x + 1) 41;
eval unquote [Int -> Int -> Int] qconst 7 99;
eval unquote [(Int -> Int) -> Int -> Int] qapply (\(x : Int). x * x) 6;
eval unquote [Int -> Int] qredex 42;
eval unquote [forall a. a -> a] qpolyId [Int] 99;
eval unquote [forall a. forall b. a -> b -> a] qpolyConst [Int] [Bool] 77 true;
eval unquote [Int -> Int] qtyRedex 17;

-- ---------- operation 2: size (F = K Int) --------------------------------

let size : forall a. Exp a -> Int =
  /\a. \(e : Exp a).
    e [K Int]
      (/\a. /\b. \(f : Int -> Int). 1 + f 0)
      (/\a. /\b. \(f : Int). \(x : Int). 1 + f + x)
      (/\(B : * -> *). \(f : forall a. Int). 1 + f [Int])
      (/\(B : * -> *). /\a. \(n : Int). 1 + n);

eval size [Int -> Int] qid;
eval size [(Int -> Int) -> Int -> Int] qself;
eval size [Int -> Int -> Int] qconst;
eval size [(Int -> Int) -> Int -> Int] qapply;
eval size [Int -> Int] qredex;
eval size [forall a. a -> a] qpolyId;
eval size [forall a. forall b. a -> b -> a] qpolyConst;
eval size [Int -> Int] qtyRedex;

-- ---------- operation 3: isAbs (F = K Bool) ------------------------------
-- True only when the term is a value-level abstraction (\) at the top.

let isAbs : forall a. Exp a -> Bool =
  /\a. \(e : Exp a).
    e [K Bool]
      (/\a. /\b. \(_f : Bool -> Bool). true)
      (/\a. /\b. \(_f : Bool). \(_x : Bool). false)
      (/\(B : * -> *). \(_f : forall a. Bool). false)
      (/\(B : * -> *). /\a. \(_n : Bool). false);

eval isAbs [Int -> Int] qid;
eval isAbs [Int -> Int -> Int] qconst;
eval isAbs [(Int -> Int) -> Int -> Int] qapply;
eval isAbs [Int -> Int] qredex;
eval isAbs [forall a. a -> a] qpolyId;
eval isAbs [Int -> Int] qtyRedex;

-- ---------- operation 4: isNF (F = K (Pair Bool Bool)) -------------------
-- Track (isNormal, isNeutral) per subterm. Both Abs and TAbs are normal iff
-- body is normal, never neutral. Both App and TApp are normal/neutral iff
-- head is neutral (App also requires the value-arg to be normal).

type NF = Pair Bool Bool;

let isNF : forall a. Exp a -> Bool =
  /\a. \(e : Exp a).
    fst [Bool] [Bool]
      (e [K NF]
        (/\a. /\b. \(f : NF -> NF).
          let body = f (mkPair [Bool] [Bool] true true) in
          mkPair [Bool] [Bool] (fst [Bool] [Bool] body) false)
        (/\a. /\b. \(f : NF). \(x : NF).
          let r = snd [Bool] [Bool] f && fst [Bool] [Bool] x in
          mkPair [Bool] [Bool] r r)
        (/\(B : * -> *). \(f : forall a. NF).
          let body = f [Int] in
          mkPair [Bool] [Bool] (fst [Bool] [Bool] body) false)
        (/\(B : * -> *). /\a. \(f : NF).
          let r = snd [Bool] [Bool] f in
          mkPair [Bool] [Bool] r r));

eval isNF [Int -> Int] qid;
eval isNF [Int -> Int -> Int] qconst;
eval isNF [(Int -> Int) -> Int -> Int] qapply;
eval isNF [Int -> Int] qredex;
eval isNF [forall a. a -> a] qpolyId;
eval isNF [forall a. forall b. a -> b -> a] qpolyConst;
eval isNF [Int -> Int] qtyRedex;

-- ---------- operation 5: CPS (F = CPS) ----------------------------------
-- The continuation-passing-style translation. Unlike the previous four
-- interpretations, CPS changes the answer type: cps : Exp a -> CPS a where
-- CPS a = forall r. (a -> r) -> r. The trick is that whenever we need a
-- direct value of type b from a CPS b, we instantiate CPS b at r := b and
-- pass the identity continuation.

type CPS = lam (a : *). forall r. (a -> r) -> r;

let cps : forall a. Exp a -> CPS a =
  /\a. \(e : Exp a).
    e [CPS]
      (/\a. /\b. \(f : CPS a -> CPS b). /\r. \(k : (a -> b) -> r).
        k (\(x : a).
          (f (/\r1. \(k1 : a -> r1). k1 x)) [b] (\(y : b). y)))
      (/\a. /\b. \(f : CPS (a -> b)). \(x : CPS a). /\r. \(k : b -> r).
        f [r] (\(g : a -> b). x [r] (\(v : a). k (g v))))
      (/\(B : * -> *). \(f : forall a. CPS (B a)). /\r. \(k : (forall a. B a) -> r).
        k (/\a. (f [a]) [B a] (\(y : B a). y)))
      (/\(B : * -> *). /\a. \(f : CPS (forall c. B c)). /\r. \(k : B a -> r).
        f [r] (\(g : forall c. B c). k (g [a])));

-- Extract a value from CPS by instantiating at the answer type and passing
-- the identity continuation.
eval cps [Int -> Int] qid [Int -> Int] (\(f : Int -> Int). f);
eval cps [Int -> Int] qid [Int] (\(f : Int -> Int). f 99);
eval cps [(Int -> Int) -> Int -> Int] qapply [Int] (\(g : (Int -> Int) -> Int -> Int). g (\(x : Int). x + x) 21);
eval cps [forall a. a -> a] qpolyId [Int] (\(p : forall a. a -> a). p [Int] 77);
eval cps [Int -> Int] qredex [Int] (\(f : Int -> Int). f 5);
eval cps [Int -> Int] qtyRedex [Int] (\(f : Int -> Int). f 8);

-- ---------- operation 6: depth (F = K Int) -------------------------------
-- Maximum nesting depth of the AST. Same shape as size but uses max instead
-- of sum at App/TApp. For qredex the head and arg are independent branches,
-- so depth = 1 + max(depth head, depth arg) is strictly less than size.

let max : Int -> Int -> Int = \(x : Int). \(y : Int). if x < y then y else x;

let depth : forall a. Exp a -> Int =
  /\a. \(e : Exp a).
    e [K Int]
      (/\a. /\b. \(f : Int -> Int). 1 + f 0)
      (/\a. /\b. \(f : Int). \(x : Int). 1 + max f x)
      (/\(B : * -> *). \(f : forall a. Int). 1 + f [Int])
      (/\(B : * -> *). /\a. \(n : Int). 1 + n);

eval depth [Int -> Int] qid;
eval depth [Int -> Int -> Int] qconst;
eval depth [(Int -> Int) -> Int -> Int] qapply;
eval depth [Int -> Int] qredex;
eval depth [forall a. a -> a] qpolyId;
eval depth [forall a. forall b. a -> b -> a] qpolyConst;
eval depth [Int -> Int] qtyRedex;

-- ---------- additional represented terms --------------------------------
-- qcompose : /\a b c. \f g x. f (g x)  - exercises nested App
-- qtwice   : /\a. \f x. f (f x)        - higher-order, shares a variable

let qcompose : Exp (forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c) =
  /\(F : * -> *). \(ab : Abs F). \(ap : App F). \(tab : TAbs F). \(_tap : TApp F).
    tab [lam a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c]
      (/\a. tab [lam b. forall c. (b -> c) -> (a -> b) -> a -> c]
        (/\b. tab [lam c. (b -> c) -> (a -> b) -> a -> c]
          (/\c. ab [b -> c] [(a -> b) -> a -> c]
            (\(f : F (b -> c)). ab [a -> b] [a -> c]
              (\(g : F (a -> b)). ab [a] [c]
                (\(x : F a). ap [b] [c] f (ap [a] [b] g x)))))));

let qtwice : Exp (forall a. (a -> a) -> a -> a) =
  /\(F : * -> *). \(ab : Abs F). \(ap : App F). \(tab : TAbs F). \(_tap : TApp F).
    tab [lam a. (a -> a) -> a -> a]
      (/\a. ab [a -> a] [a -> a]
        (\(f : F (a -> a)). ab [a] [a]
          (\(x : F a). ap [a] [a] f (ap [a] [a] f x))));

eval unquote [forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c] qcompose [Int] [Int] [Int] (\(x : Int). x + 1) (\(x : Int). x * 2) 10;
eval unquote [forall a. (a -> a) -> a -> a] qtwice [Int] (\(x : Int). x + 3) 4;
eval size [forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c] qcompose;
eval size [forall a. (a -> a) -> a -> a] qtwice;
eval depth [forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c] qcompose;
eval depth [forall a. (a -> a) -> a -> a] qtwice;
eval isNF [forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c] qcompose;
eval isNF [forall a. (a -> a) -> a -> a] qtwice;
