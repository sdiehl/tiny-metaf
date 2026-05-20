let id : forall a. a -> a = /\a. \(x : a). x;
let apply : forall a. forall b. (a -> b) -> a -> b =
  /\a. /\b. \(f : a -> b). \(x : a). f x;

eval id [Int] 5;
eval id [Bool] true;
eval apply [Int] [Int] (\(n : Int). n * n) 7;
