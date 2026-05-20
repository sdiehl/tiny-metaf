type C = lam (a : *). lam (b : *). a;

let capture : forall b. C b Int -> b = /\b. \(x : C b Int). x;
eval capture [Int] 42;
