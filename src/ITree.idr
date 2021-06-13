module ITree
import Control.Monad.State

-- Based on https://arxiv.org/pdf/1906.00046.pdf

data ITree : (e : Type -> Type) -> (r : Type) -> Type where
  Ret : r -> ITree e r
  Tau : Inf (ITree e r) -> ITree e r
  Vis : e a -> (a -> Inf (ITree e r)) -> ITree e r

implementation Functor (ITree e) where
  map f (Ret x) = Ret $ f x
  map f (Tau tr) = map f tr
  map f (Vis e k) = Vis e (\x => map f (k x))

implementation Applicative (ITree e) where
  pure a = Ret a

  (Ret f) <*> tra = map f tra
  (Tau trf) <*> tra = trf <*> tra
  (Vis e k) <*> tra = Vis e (\x => k x <*> tra)

implementation Monad (ITree e) where
  (Ret r) >>= f = f r
  (Tau tr) >>= f = Tau $ tr >>= f
  (Vis e f') >>= f = Vis e (\x => f' x >>= f)

interp : Monad m => ({r : Type} -> e r -> m r) -> {r : Type} -> ITree e r -> m r

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


handlerState : StateE s r -> StateT s (ITree e) r
handlerState Get = ST $ \s => Ret (s, s)
handlerState (Put s') = ST $ \s => Ret ((), s')

interpState : ITree (StateE s) r -> StateT s (ITree e) r
interpState = interp handlerState
