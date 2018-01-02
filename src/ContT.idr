module ContT

import Control.Monad.Identity
import Control.Monad.Trans

%access public export

data ContT : (r : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  ContK : ((a -> m r) -> m r) -> ContT r m a

Cont : Type -> Type -> Type
Cont r a = ContT r Identity a

Functor (ContT r m) where
  map f (ContK c) = ContK (\k => c (\a => k (f a)))

Applicative (ContT r m) where
  pure a = ContK (\k => k a)
  (ContK cf) <*> (ContK c) = ContK (\k => c (\a => cf (\f => k (f a))))

Monad (ContT r m) where
  (ContK c) >>= f = ContK (\k => c (\a => let (ContK k') = f a in k' k))

MonadTrans (ContT r) where
  lift x = ContK (\k => x >>= k)


run : (a -> m r) -> ContT r m a -> m r
run f (ContK c) = c f

reset : Monad m => ContT r m r -> m r
reset (ContK c) = c (\x => pure x)

shift : Monad m => ((a -> m r) -> ContT r m r) -> ContT r m a
shift f = ContK (\k => reset (f k))

callCC : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = ContK (\k => let (ContK c) = f (\a => ContK (\k' => k a)) in c k)
