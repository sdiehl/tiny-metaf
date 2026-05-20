-- Brown & Palsberg, Section 5: the deep self-representation requires F-omega.
-- The representation parametrizes an expression type by a type constructor
-- F : * -> *, then picks different F to derive different interpretations
-- (unquote, isAbs, size, CPS) from one representation.
--
-- This example showcases the F-omega ingredients that Section 5 relies on:
-- kinds beyond *, type-level lambdas, type-level application, and types
-- that are polymorphic in a type constructor.

-- Identity type operator.
type Id = lam (a : *). a;

-- Constant type operator: K a b = a.
type K = lam (a : *). lam (b : *). a;

-- Composition of two type constructors.
type Compose = lam (F : * -> *). lam (G : * -> *). lam (a : *). F (G a);

-- (lam a. a) Int reduces to Int, so an Id Int is just an Int.
let one : Id Int = 1;
eval one;

let dbl : Id Int -> Id Int = \(x : Int). x + x;
eval dbl 21;

-- HOAS-style constructors, parametrized by an interpretation F.
-- Abs F a b = (F a -> F b) -> F (a -> b).
-- App F a b = F (a -> b) -> F a -> F b.
type Abs = lam (F : * -> *). forall a. forall b. (F a -> F b) -> F (a -> b);
type App = lam (F : * -> *). forall a. forall b. F (a -> b) -> F a -> F b;

-- An expression of "type" a, parametric in the interpretation F.
type Exp = lam (a : *). forall (F : * -> *). Abs F -> App F -> F a;

-- A represented function: \(x : Int). x.
let qid : Exp (Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F).
    ab [Int] [Int] (\(x : F Int). x);

-- A represented self-application: \(x : Int -> Int). x.
-- The body returns the input (an F (Int -> Int)) unchanged.
let qself : Exp ((Int -> Int) -> Int -> Int) =
  /\(F : * -> *). \(ab : Abs F). \(_ap : App F).
    ab [Int -> Int] [Int -> Int] (\(x : F (Int -> Int)). x);

-- Choose F = Id (interpret as values).
-- Abs Id a b = (a -> b) -> (a -> b), so the abstraction passes the function through.
-- App Id a b = (a -> b) -> a -> b, plain application.
let absId : Abs Id = /\a. /\b. \(f : a -> b). f;
let appId : App Id = /\a. /\b. \(f : a -> b). \(x : a). f x;

eval qid [Id] absId appId 7;
eval qself [Id] absId appId (\(x : Int). x + 1) 41;

-- Choose F = K Int (a "size" functor: every node has size Int).
-- Abs (K Int) a b = (Int -> Int) -> Int, addition gives "size with 1 + body".
-- App (K Int) a b = Int -> Int -> Int, addition gives "1 + f + x".
let absSize : Abs (K Int) = /\a. /\b. \(f : Int -> Int). 1 + f 0;
let appSize : App (K Int) = /\a. /\b. \(f : Int). \(x : Int). 1 + f + x;

eval qid [K Int] absSize appSize;
eval qself [K Int] absSize appSize;
