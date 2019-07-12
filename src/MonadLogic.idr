module MonadLogic

-- Based on http://okmij.org/ftp/papers/LogicT.pdf
-- http://hackage.haskell.org/package/logict-0.7.0.1/docs/Control-Monad-Logic.html

import Control.Monad.Identity
import Control.Monad.Trans

interface Monad m => MonadPlus (m : Type -> Type) where
    mplus : m a -> m a -> m a
    mzero : m a

MonadPlus List where
  mplus = (++)
  mzero = []

interface MonadPlus m => MonadLogic (m : Type -> Type) where
  msplit : m a -> m (Maybe (a, m a))
  interleave : m a -> m a -> m a
  bind : m a -> (a -> m b) -> m b
  ifte : m a -> (a -> m b) -> m b -> m b
  once : m a -> m a


reflect : MonadLogic m => Maybe (a, m a) -> m a
reflect Nothing = mzero
reflect (Just (a, m)) = pure a `mplus` m

interleave' : MonadLogic m => m a -> m a -> m a
interleave' m1 m2 = do r <- msplit m1
                       case r of
                        Nothing => m2
                        Just (a, m1') => (pure a) `mplus` (interleave' m2 m1')

bind' : MonadLogic m => m a -> (a -> m b) -> m b
bind' ma f = do r <- msplit ma
                case r of
                 Nothing => mzero
                 Just (a, m') => interleave (f a) (m' `bind'` f)

ifte' : MonadLogic m => m a -> (a -> m b) -> m b -> m b
ifte' t th el = do r <- msplit t
                   case r of
                    Nothing => el
                    Just (a, m') => (th a) `mplus` (m' >>= th)

once' : MonadLogic m => m a -> m a
once' m = do r <- msplit m
             case r of
               Nothing => mzero
               Just (a, _) => pure a

data LogicT : (m : Type -> Type) -> (a : Type) -> Type where
    LT : ({r : Type} -> (a -> m r -> m r) -> m r -> m r) -> LogicT m a

Functor (LogicT m) where
  map f (LT g) = LT $ \sk, fk => g (sk . f) fk

Applicative (LogicT m) where
  pure a = LT $ \sk, fk => sk a fk
  (LT f) <*> (LT g) = LT $ \sk, fk => f (\sk', fk' => g (sk . sk') fk') fk

Monad (LogicT m) where
  (LT g) >>= f = LT $ \sk, fk => g (\a, fk' => let (LT g') = f a in g' sk fk') fk

MonadPlus (LogicT m) where
  mzero = LT $ \sk, fk => fk
  mplus (LT f) (LT f') = LT $ \sk, fk => f sk (f' sk fk)

MonadTrans LogicT where
  lift m = LT $ \sk, fk => m >>= \a => sk a fk

Monad m => MonadLogic (LogicT m) where
  msplit (LT f) = lift $ f (\a, fk => pure $ Just (a, lift fk >>= reflect)) (pure Nothing)
  interleave = interleave'
  bind = bind'
  ifte = ifte'
  once = once'

observe : Monad m => Nat -> LogicT m a -> m (List a)
observe Z _ = pure []
observe (S n) m = let (LT f) = msplit m in f sk (pure [])
  where
    sk : {a : Type, m : Type -> Type} -> Monad m => Maybe (a, LogicT m a) -> m (List a) -> m (List a)
    sk Nothing m = pure []
    sk (Just (a, m')) m = map (\xs => a :: xs) (observe n m')

ones : MonadPlus m => Int -> m Int
ones n = if n <= 0 then mzero else (pure 1) `mplus` (ones (n - 1))

zeros : MonadPlus m => Int -> m Int
zeros n = if n <= 0 then mzero else (pure 0) `mplus` (zeros (n - 1))
