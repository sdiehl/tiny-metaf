type T = Int;
let g : forall T. T -> Int = /\T. \(x : T). x;
eval g [Bool] true + 1;
