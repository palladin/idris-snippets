module Ordinals

data Ord : Type where
  Zero : Ord
  Suc  : (x : Ord) -> Ord
  Lim  : (f : Nat -> Ord) -> Ord

(+) : Ord -> Ord -> Ord
(+) Zero m = m
(+) (Suc n) m = Suc $ n + m
(+) (Lim f) m = Lim (\x => f x + m)

(*) : Ord -> Ord -> Ord
(*) Zero m = Zero
(*) (Suc n) m = n + m
(*) (Lim f) m = Lim (\x => f x * m)

exp : Ord -> Ord -> Ord
exp Zero m = Suc Zero
exp (Suc n) m = n * m
exp (Lim f) m = Lim (\x => exp (f x) m)


omega : Ord
omega = Lim rec
  where
    rec : Nat -> Ord
    rec Z = Zero
    rec (S n) = Suc $ rec n

epsilonNought : Ord
epsilonNought = Lim rec
  where
    rec : Nat -> Ord
    rec Z = omega
    rec (S n) = exp omega (rec n)
