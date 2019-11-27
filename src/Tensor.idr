module Tensor

-- Based on https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf
import src.GenericArity
import Data.Vect
import Data.HVect
import Data.Matrix.Numeric

%access public export

data Tensor : Vect n Nat -> Type -> Type where
  Scalar : a -> Tensor [] a
  Prism : Tensor ns (Vect n a) -> Tensor (n :: ns) a

toVectT : Vect n Nat -> Type -> Type
toVectT [] a = a
toVectT (x :: xs) a = toVectT xs (Vect x a)

toVectT' : Vect n Nat -> Type -> Type
toVectT' [] a = a
toVectT' (x :: xs) a = Vect x (toVectT' xs a)

toTensor : toVectT xs a -> Tensor xs a
toTensor {xs = []} v = Scalar v
toTensor {xs = (x :: xs)} v = Prism (toTensor v)

toVect : Tensor xs a -> toVectT xs a
toVect {xs = []} (Scalar v) = v
toVect {xs = (x :: xs)} (Prism v) = toVect v

finToInt : Fin n -> Int
finToInt FZ     = 0
finToInt (FS k) = 1 + finToInt k

index' : {xs : Vect n Nat} -> HVect (map (\n => Fin n) xs) -> toVectT' xs a -> a
index' {xs = []} [] x = x
index' {xs = (x :: xs)} (fin :: fins) vs = index' fins (Data.Vect.index fin vs)

index : Fin n -> Fin m -> Vect n (Vect m a) -> a
index {n} {m} fn fm xss = index' {xs = [n, m]} [fn, fm] xss

positions' : (n : Nat) -> Vect n (Fin n)
positions' Z = []
positions' (S n) = FZ :: map FS (positions' n)

tabulate' : {xs : Vect n Nat} -> (Arrows n (map (\n => Fin n) xs) a) -> toVectT' xs a
tabulate' {n = Z} {xs = []} x = x
tabulate' {n = S n} {xs = (x :: xs)} f = [tabulate' (f fn) | fn <- positions' x]

tabulate : (Fin n -> a) -> Vect n a
tabulate {n} f = tabulate' {xs = [n]} f

Functor (Tensor ns) where
  map f (Scalar x) = Scalar (f x)
  map f (Prism x) = Prism (map (map f) x)

Foldable (Tensor ns) where
  foldr {ns = []} f acc (Scalar x) = f x acc
  foldr {ns = (n :: ns)} f acc (Prism x) = foldr (\x, acc => foldr f acc x) acc x

Applicative (Tensor ns) where
  pure {ns = []} x = Scalar x
  pure {ns = (n :: ns)} x = Prism (pure (pure x))

  (<*>) {ns = []} (Scalar f) (Scalar x) = Scalar (f x)
  (<*>) {ns = (n :: ns)} (Prism f) (Prism x) = Prism ((<*>) <$> f <*> x)

Traversable (Tensor ns) where
  traverse {ns = []} f (Scalar x) = map Scalar (f x)
  traverse {ns = (n :: ns)} f (Prism x) = map Prism (traverse (traverse f) x)

Show a => Show (Tensor ns a) where
  show (Scalar x) = show x
  show (Prism x) = show x

Num a => Num (Tensor ns a) where
  (+) {ns = []} (Scalar x) (Scalar y) = Scalar (x + y)
  (+) {ns = (n :: ns)} (Prism x) (Prism y) = Prism (x + y)
  (*) {ns = []} (Scalar x) (Scalar y) = Scalar (x * y)
  (*) {ns = (n :: ns)} (Prism x) (Prism y) = Prism (x * y)
  fromInteger {ns = []} i = Scalar (fromInteger i)
  fromInteger {ns = (n :: ns)} i = Prism (fromInteger i)


example : Tensor [2, 2] Int
example = Prism (Prism (Scalar [[1, 2], [3, 4]]))

test : Tensor [2, 2] Int
test = map (\x => x * 2) example
