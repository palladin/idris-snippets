module Adjoint
import Data.Morphisms


interface (Functor f, Functor g) => Adjoint (f : Type -> Type) (g : Type -> Type) where
  unit : a -> g (f a)
  counit : f (g a) -> a

phi : Adjoint f g => (f a -> b) -> a -> g b
phi f = map f . unit

psi : Adjoint f g => (a -> g b) -> f a -> b
psi f = counit . map f

Adjoint (Pair a) (Morphism a) where
  unit x = Mor (\y => (y, x))
  counit (x, Mor f) = f x

record Compose (f : Type -> Type) (g : Type -> Type) (a : Type) where
  constructor Comp
  getComp : f (g a)

(Functor f, Functor g) => Functor (Compose f g) where
  map f = Comp . map (map f) . getComp

interface Functor m => Monad' (m : Type -> Type) where
  eta : a -> m a
  mu  : m (m a) -> m a

  (>>=) : m a -> (a -> m b) -> m b
  ma >>= f = (mu . map f) ma

Adjoint f g => Monad' (Compose g f) where
  eta x = Comp (unit x)
  mu = Comp . map (counit . map getComp) . getComp

get : Compose (Morphism s) (Pair s) s
get = (Comp (Mor (\st => (st, st))))

set : s -> Compose (Morphism s) (Pair s) ()
set st = (Comp (Mor (\_ => (st, ()))))

example : Monad' (Compose (Morphism Int) (Pair Int)) => Compose (Morphism Int) (Pair Int) ()
example = do st <- get
             set (st + 1)
             eta ()

test : Int -> (Int, ())
test = applyMor (getComp example)
