module Russell

-- Based on https://github.com/agda/agda/blob/master/test/Succeed/Russell.agda

data U : Type where
  Set : (I : Type) -> (I -> U) -> U

Regular : U -> Type
Regular (Set I f) = (i : I) -> (f i = Set I f) -> Void

R : U
R = Set (DPair U Regular) fst

notRegular : Regular R -> Void
notRegular reg = reg (R ** reg) Refl

transport : {A : Type} -> (C : A -> Type) -> {x : A} -> {y : A} -> x = y -> C x -> C y
transport _ Refl ca = ca

regular : Regular R
regular (x ** pf) eq = transport Regular eq pf (x ** pf) eq

absurd : Void
absurd = notRegular regular
