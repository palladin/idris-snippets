module ZipFolds

-- Based on http://okmij.org/ftp/Haskell/zip-folds.lhs

data FR : (a : Type) -> Type where
  Cont : ({r : Type} -> (a -> r -> r) -> r -> r) -> FR a

ofList : List a -> FR a
ofList l = Cont (\f, r => foldr f r l)

toList : FR a -> List a
toList (Cont f) = f (::) []

map : (a -> b) -> FR a -> FR b
map f (Cont g) = Cont (\h => g (\x, r => h (f x) r))

filter : (a -> Bool) -> FR a -> FR a
filter f (Cont g) = Cont (\h => g (\x, r => if f x then h x r else r))

drop : Int -> FR a -> FR a
drop n (Cont f) = Cont (\g, z => let f' = f (acc g) (seed z) in f' n)
  where
    acc : (a -> r -> r) -> a -> (Int -> r) -> Int -> r
    acc f x r n = if n <= 0 then f x (r n) else r (n - 1)
    seed : r -> Int -> r
    seed x _ = x

zipWith : (a -> b -> c) -> FR a -> FR b -> FR c
zipWith t (Cont f) fr = Cont (\g, z => let f' = f (acc z g) (seed z) in f' fr)
  where
    acc : r -> (c -> r -> r) -> a -> (FR b -> r) -> FR b -> r
    acc z f x r (Cont r2) = r2 (\y, _ => f (t x y) (r (drop 1 (Cont r2)))) z
    seed : r -> FR b -> r
    seed x _ = x

stream : FR Int
stream = ofList [1..10]

test : List (Int, Int)
test = toList $ zipWith (\x, y => (x, y)) stream stream
