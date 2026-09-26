let k : forall a. a -> forall a. a -> a = /\a. \(x : a). /\a. \(y : a). y;
let k2 : forall a. a -> forall b. b -> a = /\a. \(x : a). /\a. \(y : a). x;
eval k2 [Int] 1 [Bool] true;
