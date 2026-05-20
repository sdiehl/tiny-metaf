let fact : Int -> Int =
  fix f : Int -> Int.
    \(n : Int). if n == 0 then 1 else n * f (n - 1);

let fib : Int -> Int =
  fix f : Int -> Int.
    \(n : Int). if n < 2 then n else f (n - 1) + f (n - 2);

eval fact 0;
eval fact 5;
eval fact 10;
eval fib 10;
eval fib 15;
