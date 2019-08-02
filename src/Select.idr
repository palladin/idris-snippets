module Select

-- Based on http://eptcs.web.cse.unsw.edu.au/paper.cgi?MSFP2014.3.pdf
--          https://downloads.haskell.org/~ghc/latest/docs/html/libraries/transformers-0.5.6.2/src/Control-Monad-Trans-Select.html#SelectT

import Data.Vect
import Control.Monad.Identity
import Control.Monad.Trans

data SelectT : (r : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  Sel : ((a -> m r) -> m a) -> SelectT r m a

Select : Type -> Type -> Type
Select a r = SelectT r Identity a

Functor m => Functor (SelectT r m) where
  map f (Sel g) = Sel (\k => map f $ g (k . f))

Monad m => Applicative (SelectT r m) where
  pure a = Sel (\k => pure a)

  (Sel gf) <*> (Sel g) = Sel $ \k => do f <- gf (\f => h f k >>= k)
                                        h f k
    where
     h : (a -> b) -> (b -> m r) -> m b
     h f k = map f $ g (k . f)

Monad m => Monad (SelectT r m) where
  (Sel g) >>= f = Sel $ \k => do a <- g (\a => h a k >>= k)
                                 h a k
    where
      h : a -> (b -> m r) -> m b
      h a k = let (Sel g') = f a in g' k

MonadTrans (SelectT r) where
  lift m = Sel (\k => m)

boundedBinarySearch : Monad m => (n : Nat) -> SelectT Bool m (Vect n Bool)
boundedBinarySearch n = sequence $ replicate n $ Sel (\k => k True)
