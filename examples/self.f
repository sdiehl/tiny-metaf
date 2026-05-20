type Expr = forall r.
    (Int -> r)
 -> (r -> r -> r)
 -> (r -> r -> r)
 -> (r -> r -> r -> r)
 -> r;

let cConst : Int -> Expr =
  \(n : Int). /\r.
    \(c : Int -> r). \(_a : r -> r -> r). \(_m : r -> r -> r). \(_i : r -> r -> r -> r).
    c n;

let cAdd : Expr -> Expr -> Expr =
  \(x : Expr). \(y : Expr). /\r.
    \(c : Int -> r). \(a : r -> r -> r). \(m : r -> r -> r). \(i : r -> r -> r -> r).
    a (x [r] c a m i) (y [r] c a m i);

let cMul : Expr -> Expr -> Expr =
  \(x : Expr). \(y : Expr). /\r.
    \(c : Int -> r). \(a : r -> r -> r). \(m : r -> r -> r). \(i : r -> r -> r -> r).
    m (x [r] c a m i) (y [r] c a m i);

let cIf0 : Expr -> Expr -> Expr -> Expr =
  \(p : Expr). \(t : Expr). \(e : Expr). /\r.
    \(c : Int -> r). \(a : r -> r -> r). \(m : r -> r -> r). \(i : r -> r -> r -> r).
    i (p [r] c a m i) (t [r] c a m i) (e [r] c a m i);

let interp : Expr -> Int =
  \(e : Expr). e [Int]
    (\(n : Int). n)
    (\(x : Int). \(y : Int). x + y)
    (\(x : Int). \(y : Int). x * y)
    (\(p : Int). \(t : Int). \(f : Int). if p == 0 then t else f);

let size : Expr -> Int =
  \(e : Expr). e [Int]
    (\(_n : Int). 1)
    (\(x : Int). \(y : Int). x + y + 1)
    (\(x : Int). \(y : Int). x + y + 1)
    (\(p : Int). \(t : Int). \(f : Int). p + t + f + 1);

let depth : Expr -> Int =
  \(e : Expr). e [Int]
    (\(_n : Int). 1)
    (\(x : Int). \(y : Int). (if x < y then y else x) + 1)
    (\(x : Int). \(y : Int). (if x < y then y else x) + 1)
    (\(p : Int). \(t : Int). \(f : Int).
       (if p < t then (if t < f then f else t) else (if p < f then f else p)) + 1);

let prog : Expr =
  cIf0 (cAdd (cConst 1) (cConst 2))
       (cConst 100)
       (cMul (cConst 6) (cAdd (cConst 3) (cConst 4)));

eval interp prog;
eval size prog;
eval depth prog;
