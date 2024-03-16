module RelativeMonad

-- Based on https://www.researchgate.net/publication/286096562_Relative_Monads_Formalised

record Monoid where
  constructor MkMonoid
  S : Type
  e : S
  (.) : S -> S -> S
  lid : {m : S} -> e . m = m
  rid : {m : S} -> m . e = m
  assoc : {m, n, o : S} -> (m . n) . o = m . (n . o)

NatMonoid : Monoid
NatMonoid = MkMonoid
  Nat
  0
  (+)
  Refl
  plusZeroRight
  plussassoc
  where
    plussassoc : {m, n, o : Nat} -> (m + n) + o = m + (n + o)
    plussassoc {m} {n} {o} = sym (plusAssociative m n o)

    plusZeroRight : {m : Nat} -> m + 0 = m
    plusZeroRight {m} = plusZeroRightNeutral m

record Cat where
  constructor MkCat
  Obj : Type
  Hom : Obj -> Obj -> Type
  iden : {x : Obj} -> Hom x x
  comp : {x, y, z : Obj} -> Hom y z -> Hom x y -> Hom x z
  idl : {x, y : Obj} -> {f : Hom x y} -> comp iden f = f
  idr : {x, y : Obj} -> {f : Hom x y} -> comp f iden = f
  assoc : {w, x, y, z : Obj} -> {f : Hom y z} -> {g : Hom x y} -> {h : Hom w x} ->
            comp (comp f g) h = comp f (comp g h)

TypeCat : Cat
TypeCat = MkCat
  Type
  TypeMorph
  id
  (.)
  Refl
  Refl
  Refl
  where
    TypeMorph : Type -> Type -> Type
    TypeMorph a b = a -> b

Op : Cat -> Cat
Op cat = MkCat
  (Obj cat)
  (\x, y => Hom cat y x)
  (iden cat)
  (\f, g => comp cat g f)
  (idr cat)
  (idl cat)
  (sym (assoc cat))
