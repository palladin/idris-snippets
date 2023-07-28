module Delim

mutual
  data CC : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> Type where
    MkCC : (a -> m w) -> ({x : Type} -> SubCont p m x a -> p m x -> m w) -> CC p m a

  SubCont : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> (b : Type) -> Type
  SubCont p m a b = CC p m a -> CC p m b

  CCT : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (a : Type) -> (w : Type) -> Type
  CCT p m a w = SubCont p m a w -> CC p m w

  data Prompt : (p : (Type -> Type) -> Type -> Type) -> (m : Type -> Type) -> (w : Type) -> Type where
    MkPrompt : (CCT p m x w -> p m x) ->  (p m x -> Maybe (CCT p m x w)) -> Prompt p m w
