type Nat = forall a. (a -> a) -> a -> a;

let zero : Nat = /\a. \(s : a -> a). \(z : a). z;
let one  : Nat = /\a. \(s : a -> a). \(z : a). s z;
let two  : Nat = /\a. \(s : a -> a). \(z : a). s (s z);

let succ : Nat -> Nat =
  \(n : Nat). /\a. \(s : a -> a). \(z : a). s (n [a] s z);

let plus : Nat -> Nat -> Nat =
  \(m : Nat). \(n : Nat). /\a. \(s : a -> a). \(z : a). m [a] s (n [a] s z);

let mul : Nat -> Nat -> Nat =
  \(m : Nat). \(n : Nat). /\a. \(s : a -> a). m [a] (n [a] s);

let to_int : Nat -> Int =
  \(n : Nat). n [Int] (\(k : Int). k + 1) 0;

let three : Nat = succ two;
let five  : Nat = plus two three;
let six   : Nat = mul two three;

eval to_int zero;
eval to_int five;
eval to_int six;
eval to_int (mul three three);
