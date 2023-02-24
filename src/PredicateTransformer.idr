module PredicateTransformer

-- Based on https://dl.acm.org/doi/10.1145/3341707

data Free : (c : Type) -> (r : c -> Type) -> (a : Type) -> Type where
  Pure : a -> Free c r a
  Step : (cmd : c) -> (r cmd -> Free c r a) -> Free c r a


(>>=) : Free c r a -> (a -> Free c r b) -> Free c r b
(>>=) (Pure x) f = f x
(>>=) (Step cmd k) f = Step cmd (\a => (k a) >>= f)

pure : a -> Free c r a
pure = Pure

data C : Type where
  Abort : C

R : C -> Type
R Abort = Void

Partial : Type -> Type
Partial = Free C R

abort : Partial a
abort = Step Abort void

wpPartial : {a : Type} -> {b : a -> Type} -> (f : (x : a) -> Partial (b x)) -> (p : (x : a) -> b x -> Type) -> a -> Type
wpPartial = ?fsfs

-- example
pop : List a -> Partial (a, List a)
pop [] = abort
pop (x :: xs) = pure (x, xs)

add : List Nat -> Partial (List Nat)
add xs = do (x1 , xs) <- pop xs
            (x2 , xs) <- pop xs
            pure $ (x1 + x2) :: xs

-- specification
record Spec (a : Type) (b : a -> Type) where
    constructor MkSpec
    pred : a -> Type
    post : (x : a) -> b x -> Type

SpecK : Type -> Type -> Type
SpecK a b = Spec a (\_ => b)

data Add : List Nat -> List Nat -> Type where
  AddStep : Add (x1 :: x2 :: xs) ((x1 + x2) :: xs)

addSpec : SpecK (List Nat) (List Nat)
addSpec = MkSpec pred Add
  where
    pred : List Nat -> Type
    pred [] = Void
    pred (x :: []) = Void
    pred (x :: xs) = Unit

wpSpec : Spec a b -> ((x : a) -> b x -> Type) -> a -> Type
wpSpec (MkSpec pred post) p = \x => (pred x, (bx : b x) -> post x bx -> p x bx)

refine : {a : Type} -> {b : a -> Type} -> (pt1, pt2 : ((x : a) -> b x -> Type) -> (a -> Type)) -> Type
refine {a} {b} pt1 pt2 = (p : (x : a) -> b x -> Type) -> ((x : a) -> pt1 p x -> pt2 p x)

correctness : refine (wpSpec addSpec) (wpPartial add)
correctness = ?dfsdfs
