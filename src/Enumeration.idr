module Enumeration

-- Based on https://dl.acm.org/doi/abs/10.1145/3547636

Enumerator : Type -> Type -> Type
Enumerator a b = List a -> List b

infixr 4 <$>
(<$>) : (a -> b) -> Enumerator c a -> Enumerator c b
(<$>) f e = map f . e

mutual
  interleave' : List a -> List a -> List a
  interleave' [] ys = ys
  interleave' (x :: xs) ys = x :: interleave ys xs

  interleave : List a -> List a -> List a
  interleave [] ys = ys
  interleave (x :: xs) ys = x :: interleave' ys xs

infixr 2 <|>
(<|>) : Enumerator a b -> Enumerator a b -> Enumerator a b
(<|>) e1 e2 xs = interleave (e1 xs) (e2 xs)

prod : List a -> List b -> List (a, b)
prod [] ys = []
prod (x :: xs) [] = []
prod (x :: xs) (y :: ys) = (x,y) :: interleave (map (\y => (x,y)) ys) (prod xs (y:: ys))

infixl 3 <*>
(<*>) : Enumerator c (a -> b) -> Enumerator c a -> Enumerator c b
(<*>) e1 e2 xs = map apply (prod (e1 xs) (e2 xs))
  where
    apply : ((a -> b), a) -> b
    apply (f, x) = f x

rec : Enumerator a a
rec xs = xs

pure : b -> Enumerator a b
pure x = const [x]

iterate : Nat -> (a -> a) -> a -> a
iterate Z f x = x
iterate (S n) f x = f (iterate n f x)

enumerate : Enumerator a a -> Nat -> List a
enumerate e n = iterate n e []


data ElemOf : a -> List a -> Type where
  Here : ElemOf x (x :: xs)
  There : ElemOf x xs -> ElemOf x (y :: xs)

data Occurs : a -> Enumerator a a -> Type where
  OC : (n : Nat) ->  ElemOf x (enumerate e n) -> Occurs x e

Complete : Enumerator a a -> Type
Complete {a} e = (x : a) -> Occurs x e

Unique : List a -> Type
Unique xs = (x : a) -> (p1, p2 : ElemOf x xs) -> p1 = p2


-- Example
data Tree : Type where
  Leaf : Tree
  Node : Tree -> Tree -> Tree

trees : Enumerator Tree Tree
trees = pure Leaf <|> Node <$> rec <*> rec

nats : Enumerator Nat Nat
nats = pure Z <|> S <$> rec

test : enumerate Enumeration.nats 3 = [0, 1, 2]
test = Refl

test' : enumerate Enumeration.trees 3 = [Leaf, Node Leaf Leaf,
                                         Node Leaf (Node Leaf Leaf),
                                         Node (Node Leaf Leaf) Leaf,
                                         Node (Node Leaf Leaf) (Node Leaf Leaf)]
test' = Refl
