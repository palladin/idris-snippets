module Naperian

-- Naperian Functors, based on https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf

import Data.Vect
import Data.Fin


interface Functor f => Naperian (f : Type -> Type) where
  Log : {f : Type} -> Type
  lookup' : f a -> (Log -> a)
  positions : f Log
  tabulate : (Log -> a) -> f a

  positions = tabulate id

Naperian (Vect n) where
  Log {n} = Fin n

  lookup' [] FZ impossible
  lookup' [] (FS _) impossible
  lookup' (x :: xs) FZ = x
  lookup' (x :: xs) (FS y) = lookup' xs y

  tabulate h = map h positions
    where
      positions = positions' (replicate _ ())
        where
          positions' : Vect n () -> Vect n (Fin n)
          positions' [] = []
          positions' (() :: xs) = FZ :: map FS (positions' xs)


transpose' : (Naperian f, Naperian g) => f (g a) -> g (f a)
transpose' source = (map tabulate . tabulate . flip . lookup' . map lookup') source

example : Vect 2 (Vect 3 Integer)
example = [[1, 2, 3], [4, 5, 6]]

transposedExample : Vect 3 (Vect 2 Integer)
transposedExample = transpose' example
