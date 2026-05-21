-- shallow self-representation, plain system f. one operation: unquote.
--
--   exp t   = iota -> t            where iota = forall i. i -> i
--   unquote = /\a. \q. q (/\i. \x. x)
--
-- the trick: every application f x in the source becomes (m [type-of-f] f) x,
-- where m : iota is a marker bound at the top of the representation. this
-- freezes beta-redexes so the encoded term is already a normal form. plugging
-- m := /\i. \x. x at unquote-time releases them and we get the original term
-- back. for richer operations (size, isAbs, cps, ...) see deep.f.

type Iota = forall i. i -> i;

let unquote : forall a. (Iota -> a) -> a =
  /\a. \(q : Iota -> a). q (/\i. \(x : i). x);

-- a few host-language values to quote.
let id    : forall a. a -> a                  = /\a. \(x : a). x;
let const : forall a. a -> forall b. b -> a   = /\a. \(x : a). /\b. \(y : b). x;
let foo   : forall b. b -> (forall a. a -> a) = const [forall a. a -> a] id;

-- pure lambdas / type-lambdas don't need the marker, since they have no head
-- redex to freeze. so qid and qconst just ignore m.
let qid : Iota -> forall a. a -> a =
  \(_m : Iota). /\a. \(x : a). x;

let qconst : Iota -> forall a. a -> forall b. b -> a =
  \(_m : Iota). /\a. \(x : a). /\b. \(y : b). x;

-- qfoo encodes (const [forall a. a -> a] id). each application picks up an m.
let qfoo : Iota -> forall b. b -> (forall a. a -> a) =
  \(m : Iota).
    (m [(forall a. a -> a) -> forall b. b -> (forall a. a -> a)]
       ((m [forall a. a -> forall b. b -> a]
           (/\a. \(x : a). /\b. \(y : b). x))
        [forall a. a -> a]))
    (/\a. \(x : a). x);

eval (unquote [forall b. b -> (forall a. a -> a)] qfoo) [Int] 7 [Int] 42;

-- a first-order example: 1 + 1 frozen, then unquoted to run.
let two : Int = (\(x : Int). x + x) 1;

let qtwo : Iota -> Int =
  \(m : Iota). m [Int -> Int] (\(x : Int). x + x) 1;

eval unquote [Int] qtwo;
eval two;

-- one more: (\x y. x + y) 3 4. two applications, two markers.
let plus  : Int -> Int -> Int = \(x : Int). \(y : Int). x + y;
let seven : Int = plus 3 4;

let qseven : Iota -> Int =
  \(m : Iota).
    m [Int -> Int]
      (m [Int -> Int -> Int] (\(x : Int). \(y : Int). x + y) 3)
      4;

eval seven;
eval unquote [Int] qseven;
