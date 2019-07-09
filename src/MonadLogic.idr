module MonadLogic

-- Based on http://okmij.org/ftp/papers/LogicT.pdf
-- http://hackage.haskell.org/package/logict-0.7.0.1/docs/Control-Monad-Logic.html

import Control.Monad.Identity
import Control.Monad.Trans

interface Monad m => MonadPlus (m : Type -> Type) where
    mplus : m a -> m a -> m a
    mzero : m a

interface MonadPlus m => MonadLogic (m : Type -> Type) where
  msplit : m a -> m (Maybe (a, m a))
  
  interleave : MonadLogic m => m a -> m a -> m a
  interleave @{constr} m1 m2 = do r <- msplit m1
                                  case r of
                                    Nothing => m2
                                    Just (a, m1') => (pure a) `mplus` (interleave @{constr} m2 m1')

  bind : MonadLogic m => m a -> (a -> m b) -> m b
  bind @{constr} ma f = do r <- msplit ma
                           case r of
                             Nothing => mzero
                             Just (a, m') => interleave @{constr} (f a) (m' `bind` f)

  ifte : MonadPlus m => m a -> (a -> m b) -> m b -> m b
  ifte t th el = do r <- msplit t
                    case r of
                      Nothing => el
                      Just (a, m') => (th a) `mplus` (m' >>= th)

  once : MonadPlus m => m a -> m a
  once m = do r <- msplit m
              case r of
                Nothing => mzero
                Just (a, _) => pure a

reflect : MonadLogic m => Maybe (a, m a) -> m a
reflect Nothing = mzero
reflect (Just (a, m)) = pure a `mplus` m

data LogicT : (m : Type -> Type) -> (a : Type) -> Type where
    C : ({r : Type} -> (a -> m r -> m r) -> m r -> m r) -> LogicT m a
