module Ordinals

data Ord : Type where
  Zero : Ord
  Suc  : (x : Ord) -> Ord
  Lim  : (f : Nat -> Ord) -> Ord

(+) : Ord -> Ord -> Ord
(+) Zero m = m
(+) (Suc n) m = Suc $ n + m
(+) (Lim f) m = Lim (\x => f x + m)

omega : Ord
omega = Lim fromNat
  where
    fromNat : Nat -> Ord
    fromNat Z = Zero
    fromNat (S n) = Suc $ fromNat n
