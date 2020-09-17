module Matrix

-- Based on https://dl.acm.org/doi/10.1145/3406088.3409019

import Data.Nat.DivMod

data Shape : Type where
  Zero : Shape
  One : Shape
  Plus : Shape -> Shape -> Shape

data Matrix : (e : Type) -> (c : Shape) -> (r : Shape) -> Type where
  Elem : e -> Matrix e One One
  Join : Matrix e a r -> Matrix e b r -> Matrix e (Plus a b) r
  Fork : Matrix e c a -> Matrix e c b -> Matrix e c (Plus a b)


fromNat' : Nat -> Nat -> Shape
fromNat' k Z = Zero
fromNat' k (S Z) = One
fromNat' Z n = Zero
fromNat' (S k) n with (divMod n 1)
  fromNat' (S k) (remainder + (quotient * (S (S Z)))) | (MkDivMod quotient remainder remainderSmall) =
    let m = fromNat' k quotient in
    if remainder == Z then Plus m m else Plus One (Plus m m)

fromNat : Nat -> Shape
fromNat n = fromNat' 64 n

abideJF : Matrix e cols rows -> Matrix e cols rows
abideJF (Join (Fork a c) (Fork b d)) = Fork (Join (abideJF a) (abideJF b)) (Join (abideJF c) (abideJF d))
abideJF (Elem e) = Elem e
abideJF (Join a b) = Join (abideJF a) (abideJF b)
abideJF (Fork a b) = Fork (abideJF a) (abideJF b)

zipWithM : (e -> f -> g) -> Matrix e cols rows -> Matrix f cols rows -> Matrix g cols rows
zipWithM f (Elem a) (Elem b) = Elem (f a b)
zipWithM f (Join a b) (Join c d) = Join (zipWithM f a c) (zipWithM f b d)
zipWithM f (Fork a b) (Fork c d) = Fork (zipWithM f a c) (zipWithM f b d)
zipWithM f x@(Fork _ _) y@(Join _ _) = zipWithM f x (abideJF y)
zipWithM f x@(Join _ _) y@(Fork _ _) = zipWithM f (abideJF x) y

comp : Num e => Matrix e cr rows -> Matrix e cols cr -> Matrix e cols rows
comp (Elem a) (Elem b) = Elem (a * b)
comp (Join a b) (Fork c d) = zipWithM (+) (comp a c) (comp b d)
comp (Fork a b) c = Fork (comp a c) (comp b c)
comp c (Join a b) = Join (comp c a) (comp c b)

iden2x2 : Num e => Matrix e (fromNat 2) (fromNat 2)
iden2x2 = Fork (Join (Elem 1) (Elem 0))
               (Join (Elem 0) (Elem 1))
