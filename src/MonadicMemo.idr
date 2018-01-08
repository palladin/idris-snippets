module MonadicMemo

-- Monadic memoization, based on http://www.cs.utexas.edu/~wcook/Drafts/2006/MemoMixins.pdf

import Control.Monad.Identity
import Control.Monad.State
import Data.SortedMap

Gen : Type -> Type
Gen a = a -> a

gmFib : Monad m => Gen (Int -> m Int)
gmFib f 0 = pure 0
gmFib f 1 = pure 1
gmFib f n = do nm1 <- f (n - 1)
               nm2 <- f (n - 2)
               pure (nm1 + nm2)


fix : ((a -> b) -> (a -> b)) -> a -> b
fix f x = f (fix f) x

testIden : Int -> Int
testIden = runIdentity . (fix gmFib)

memo : MonadState (SortedMap a b) (StateT (SortedMap a b) m) => Gen (a -> StateT (SortedMap a b) m b)
memo f x = do map <- get
              apply map f x
  where
    apply : MonadState (SortedMap a b) (StateT (SortedMap a b) m) => SortedMap a b -> Gen (a -> StateT (SortedMap a b) m b)
    apply map f x with (lookup x map)
      apply map f x | Nothing = do y <- f x
                                   put (insert x y map)
                                   pure y
      apply map f x | (Just y) = pure y


testMemo : Int -> Int
testMemo x = fst . runIdentity $ runStateT (getState x) empty
  where
      getState : Int -> StateT (SortedMap Int Int) Identity Int
      getState x = fix (memo . gmFib) x
