let f : forall a. a -> forall b. b -> b = /\a. \(x : a). /\b. \(y : b). x;
eval f [Int] 1 [Bool] true && true;
