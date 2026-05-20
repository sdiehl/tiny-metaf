type Iota = forall i. i -> i;

let unquote : forall a. (Iota -> a) -> a =
  /\a. \(q : Iota -> a). q (/\i. \(x : i). x);

let two : Int = (\(x : Int). x + x) 1;

let qtwo : Iota -> Int =
  \(m : Iota). m [Int -> Int] (\(x : Int). x + x) 1;

eval two;
eval unquote [Int] qtwo;

let plus : Int -> Int -> Int = \(x : Int). \(y : Int). x + y;

let qseven : Iota -> Int =
  \(m : Iota).
    m [Int -> Int]
      (m [Int -> Int -> Int] (\(x : Int). \(y : Int). x + y) 3)
      4;

eval unquote [Int] qseven;
