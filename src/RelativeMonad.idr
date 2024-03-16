module RelativeMonad


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
