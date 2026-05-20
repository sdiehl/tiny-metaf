let id : forall a. a -> a =
  /\a. \(x : a). x;

let const : forall a. forall b. a -> b -> a =
  /\a. /\b. \(x : a). \(y : b). x;

let compose : forall a. forall b. forall c. (b -> c) -> (a -> b) -> a -> c =
  /\a. /\b. /\c. \(f : b -> c). \(g : a -> b). \(x : a). f (g x);

let inc : Int -> Int = \(n : Int). n + 1;
let dbl : Int -> Int = \(n : Int). n * 2;

eval id [Int] 42;
eval const [Int] [Bool] 7 true;
eval compose [Int] [Int] [Int] inc dbl 10;
