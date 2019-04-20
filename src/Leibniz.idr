module Leibniz
import Control.Monad.Identity


data Eq : (a : Type) -> (b : Type) -> Type where
  Subs : ({f : Type ->  Type} -> f a -> f b) -> Eq a b


refl : Eq a a
refl = Subs id

subst : {f : Type -> Type} -> Eq a b -> f a -> f b
subst (Subs subs) fa = subs fa

trans : Eq a b -> Eq b c -> Eq a c
trans ab bc = subst bc ab

cast : Eq a b -> a -> b
cast eq = runIdentity . subst eq . Id

Flip : (Type -> Type -> Type) -> Type -> Type -> Type
Flip f a b = f b a

symm : Eq a b -> Eq b a
symm eq = subst {f = Flip Eq a} eq refl
