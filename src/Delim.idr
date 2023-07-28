module Delim

import Control.Catchable


mutual
  data CC : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> Type where
    MkCC : ({w : Type} -> (a -> m w) -> ({x : Type} -> SubCont p m x a -> p m x -> m w) -> m w) -> CC p m a

  SubCont : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> (b : Type) -> Type
  SubCont p m a b = CC p m a -> CC p m b

  CCT : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> (b : Type) -> Type
  CCT p m a b = SubCont p m a b -> CC p m b

  data Prompt : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> Type where
    MkPrompt : ({x : Type} -> CCT p m x a -> p m x) ->  ({x : Type} -> p m x -> Maybe (CCT p m x a)) -> Prompt p m a

unCC : CC p m a -> ({w : Type} -> (a -> m w) -> ({x : Type} -> SubCont p m x a -> p m x -> m w) -> m w)
unCC (MkCC f) = f

pure : a -> CC p m a
pure x = MkCC $ \ki, kd => ki x

(>>=) : CC p m a -> (a -> CC p m b) -> CC p m b
m >>= f = MkCC $ \ki, kd => unCC m (\a => unCC (f a) ki kd)
                                   (\ctx => kd (\x => ctx x >>= f))

pushPrompt : Monad m => Prompt p m a -> CC p m a -> CC p m a
pushPrompt (MkPrompt inj prj) body = MkCC $ \ki, kd => unCC body ki (kd' (MkPrompt inj prj) ki kd)
  where
    kd' : {x : Type} -> Prompt p m a -> (a -> m w) -> ({x : Type} -> SubCont p m x a -> p m x -> m w) -> SubCont p m x a -> p m x -> m w
    kd' p ki kd ctx body with (prj body)
      kd' p ki kd ctx body | (Just b) = unCC (b ctx) ki kd
      kd' p ki kd ctx body | Nothing = kd (\x => pushPrompt p (ctx x)) body

takeSubCont : Monad m => Prompt p m b -> CCT p m a b -> CC p m a
takeSubCont (MkPrompt inj _) body = MkCC $ \ki, kd => kd id (inj body)

pushSubCont : Monad m => SubCont p m a b -> CC p m a -> CC p m b
pushSubCont sk cc = sk cc

runCC : (Monad m, Catchable m String) => CC p m a -> m a
runCC m = unCC m pure (\_, _ => throw "Escaping bubble: you have forgotten pushPrompt")
