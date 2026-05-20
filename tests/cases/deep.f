type Id = lam (a : *). a;
type K = lam (a : *). lam (b : *). a;

type Abs = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (a -> b);
type Exp = lam (a : *). forall (F : * -> *). Abs F -> F a;

let qid : Exp (Int -> Int) =
  /\(F : * -> *). \(ab : Abs F).
    ab [Int] [Int] (\(x : F Int). x);

let absId : Abs Id = /\a. /\b. \(f : a -> b). f;
let absSize : Abs (K Int) = /\a. /\b. \(f : Int -> Int). 1 + f 0;

eval qid [Id] absId 42;
eval qid [K Int] absSize;
