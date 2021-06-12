module ITree

-- Based on https://arxiv.org/pdf/1906.00046.pdf

data ITree : (e : Type -> Type) -> (r : Type) -> Type where
  Ret : r -> ITree e r
  Tau : Inf (ITree e r) -> ITree e r
  Vis : e a -> (a -> Inf (ITree e r)) -> ITree e r

(>>=) : ITree e r -> (r -> ITree e s) -> ITree e s
(>>=) (Ret r) f = f r
(>>=) (Tau tr) f = Tau $ tr >>= f
(>>=) (Vis e f') f = Vis e (\x => f' x >>= f)

data IO' : Type -> Type where
  Input : IO' Nat
  Output : Nat -> IO' ()


spin : ITree IO' ()
spin = Tau spin

kill9 : ITree IO' ()
kill9 = Vis Input (\x => if x == 9 then Ret () else kill9)

data StateE : (s : Type) -> Type -> Type where
  Get : StateE s s
  Put : s -> StateE s ()

StateT : (s : Type) -> (m : Type -> Type) -> (r : Type) -> Type
StateT s m r = s -> m (s , r)
