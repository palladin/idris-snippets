module Kan
import Control.Monad.Identity
import Data.Morphisms


data Ran : (f : Type -> Type) -> (g : Type -> Type) -> (a : Type) -> Type where
  R : ({b : Type} -> (a -> f b) -> g b) -> Ran f g a

data Lan : (f : Type -> Type) -> (g : Type -> Type) -> (a : Type) -> Type where
  L : (f b -> a) -> g b -> Lan f g a

Functor (Ran f g) where
  map f ran = R (\k => let (R f') = ran in f' (k . f))

Functor (Lan f g) where
  map f (L g h) = L (f . g) h

Yoneda : (Type -> Type) -> Type -> Type
Yoneda f a = Ran Identity f a

CoYoneda : (Type -> Type) -> Type -> Type
CoYoneda f a = Lan Identity f a

Codensity : (Type -> Type) -> Type -> Type
Codensity m a = Ran m m a

Reducer : Type -> Type
Reducer a = Ran Endomorphism Endomorphism a
