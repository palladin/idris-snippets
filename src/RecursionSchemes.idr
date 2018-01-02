module RecursionSchemes

data Fix : (f : Type -> Type) -> Type where
  Fx : (f (Fix f)) -> Fix f

data ListF : Type -> Type -> Type where
  Nil : ListF a f
  Cons : a -> f -> ListF a f

Functor (ListF a) where
  map f [] = []
  map f (Cons x xs) = Cons x (f xs)

List' : Type -> Type
List' a = Fix (ListF a)

nil : List' a
nil = Fx Nil

(::) : a -> List' a -> List' a
(::) x xs = Fx (Cons x xs)

cata : Functor f => (f a -> a) -> Fix f -> a
cata alg (Fx f) = (alg . map (cata alg)) f

ana : Functor f => (a -> f a) -> a -> Fix f
ana f a = (Fx . map (ana f) . f) a

hylo : Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g a = (cata f . ana g) a

-- Catamorphism examples
count : List' a -> Int
count xs = cata countF xs
  where
    countF : ListF a Int -> Int
    countF [] = 0
    countF (Cons _ c) = 1 + c

sum : List' Int -> Int
sum xs = cata sumF xs
  where
    sumF : ListF Int Int -> Int
    sumF [] = 0
    sumF (Cons x c) = x + c

example : List' Int
example = 1 :: 2 :: 3 :: 4 :: 5 :: nil

testCount : Int
testCount = count example

testSum : Int
testSum = sum example

-- Anamorphism examples
repeat : Int -> List' Int
repeat n = ana countF n
  where
    countF : Int -> ListF Int Int
    countF n = if n <= 0 then Nil else Cons n (n - 1)


testRepeat : Int
testRepeat = sum (repeat 5)
