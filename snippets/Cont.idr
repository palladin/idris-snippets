module Cont

%access public export

data Cont : (r : Type) -> (a : Type) -> Type where
  ContK : ((a -> r) -> r) -> Cont r a

Functor (Cont r) where
  map f (ContK c) = ContK (\k => c (\a => k (f a)))

Applicative (Cont r) where
  pure a = ContK (\k => k a)
  (ContK cf) <*> (ContK c) = ContK (\k => c (\a => cf (\f => k (f a))))

Monad (Cont r) where
  (ContK c) >>= f = ContK (\k => c (\a => let (ContK k') = f a in k' k))

reset : Cont r r -> r
reset (ContK c) = c id

shift : ((a -> r) -> Cont r r) -> Cont r a
shift f = ContK (\k => reset (f k))

callCC : ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = ContK (\k => let (ContK c) = f (\a => ContK (\k' => k a)) in c k)
