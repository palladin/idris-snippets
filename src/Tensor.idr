module Tensor

-- Based on https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf

import Data.Vect
import Data.Matrix.Numeric

%access public export

data Tensor : Vect n Nat -> Type -> Type where
  Scalar : a -> Tensor [] a
  Prism : Tensor ns (Vect n a) -> Tensor (n :: ns) a

toVectT : Vect n Nat -> Type -> Type
toVectT [] a = a
toVectT (x :: xs) a = toVectT xs (Vect x a)

toTensor : toVectT xs a -> Tensor xs a
toTensor {xs = []} v = Scalar v
toTensor {xs = (x :: xs)} v = Prism (toTensor v)

toVect : Tensor xs a -> toVectT xs a
toVect {xs = []} (Scalar v) = v
toVect {xs = (x :: xs)} (Prism v) = toVect v

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
