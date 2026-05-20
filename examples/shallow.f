-- Brown & Palsberg, "Breaking Through the Normalization Barrier:
-- A Self-Interpreter for F-omega" (POPL 2016).
--
-- This is the SHALLOW self-representation from Section 3, which works in
-- plain System F. (The deep representation supporting multiple operations
-- like isAbs / isNF / size / CPS requires F-omega type operators.)
--
--   Exp t   = Iota -> t              where Iota = forall i. i -> i
--   unquote : forall a. (Iota -> a) -> a
--   unquote = /\a. \q. q (/\i. \x. x)
--
-- Quotation: every term/type application of a function f gets wrapped as
-- (m [type-of-f]) f, where m : Iota is a marker bound at the top of the
-- representation. This freezes beta-redexes so the representation is in
-- normal form; plugging m := /\i. \x. x at unquote-time releases them.

type Iota = forall i. i -> i;

let unquote : forall a. (Iota -> a) -> a =
  /\a. \(q : Iota -> a). q (/\i. \(x : i). x);

let id    : forall a. a -> a                  = /\a. \(x : a). x;
let const : forall a. a -> forall b. b -> a   = /\a. \(x : a). /\b. \(y : b). x;
let foo   : forall b. b -> (forall a. a -> a) = const [forall a. a -> a] id;

let qid : Iota -> forall a. a -> a =
  \(_m : Iota). /\a. \(x : a). x;

let qconst : Iota -> forall a. a -> forall b. b -> a =
  \(_m : Iota). /\a. \(x : a). /\b. \(y : b). x;

let qfoo : Iota -> forall b. b -> (forall a. a -> a) =
  \(m : Iota).
    (m [(forall a. a -> a) -> forall b. b -> (forall a. a -> a)]
       ((m [forall a. a -> forall b. b -> a]
           (/\a. \(x : a). /\b. \(y : b). x))
        [forall a. a -> a]))
    (/\a. \(x : a). x);

eval (unquote [forall b. b -> (forall a. a -> a)] qfoo) [Int] 7 [Int] 42;

let two : Int = (\(x : Int). x + x) 1;

let qtwo : Iota -> Int =
  \(m : Iota). m [Int -> Int] (\(x : Int). x + x) 1;

eval unquote [Int] qtwo;
eval two;

-- Direct round-trip on a non-trivial first-order term: apply 3 to 4
let plus  : Int -> Int -> Int = \(x : Int). \(y : Int). x + y;
let seven : Int = plus 3 4;

let qseven : Iota -> Int =
  \(m : Iota).
    m [Int -> Int]
      (m [Int -> Int -> Int] (\(x : Int). \(y : Int). x + y) 3)
      4;

eval seven;
eval unquote [Int] qseven;
