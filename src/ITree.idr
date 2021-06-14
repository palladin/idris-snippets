module ITree
import Control.Monad.State

-- Based on https://arxiv.org/pdf/1906.00046.pdf

data ITree : (e : Type -> Type) -> (r : Type) -> Type where
  Ret : r -> ITree e r
  Tau : Inf (ITree e r) -> ITree e r
  Vis : e a -> (a -> Inf (ITree e r)) -> ITree e r

implementation Functor (ITree e) where
  map f (Ret x) = Ret $ f x
  map f (Tau tr) = Tau $ map f tr
  map f (Vis e k) = Vis e (\x => map f (k x))

implementation Applicative (ITree e) where
  pure a = Ret a

  (Ret f) <*> tra = map f tra
  (Tau trf) <*> tra = Tau $ trf <*> tra
  (Vis e k) <*> tra = Vis e (\x => k x <*> tra)

implementation Monad (ITree e) where
  (Ret r) >>= f = f r
  (Tau tr) >>= f = Tau $ tr >>= f
  (Vis e f') >>= f = Vis e (\x => f' x >>= f)

interface Monad m => MonadIter (m : Type -> Type) where
  iter : (a -> m (Either a b)) -> a -> m b

implementation MonadIter (ITree e) where
  iter body a = do {
                  ab <- body a;
                  case ab of
                    Left a => Tau $ iter body a
                    Right b => Ret b
                }

implementation MonadIter (StateT s (ITree e)) where
  iter body a = ST $ \s => let (ST f) = body a in ?sdfsf

interp : MonadIter m => ({r : Type} -> e r -> m r) -> {r : Type} -> ITree e r -> m r
interp h = iter (\tr => case tr of
                          Ret r => pure $ Right r
                          Tau tr => pure $ Left tr
                          Vis e k => h e >>= (\x => pure $ Left (k x)))

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
