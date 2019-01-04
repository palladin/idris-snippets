module FTCQueue

-- Based on http://okmij.org/ftp/Haskell/extensible/FTCQueue1.hs

data FTCQueue : (m : Type -> Type) -> a -> b -> Type where
  Leaf : (a -> m b) -> FTCQueue m a b
  Node : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b


tsingleton : (a -> m b) -> FTCQueue m a b
tsingleton r = Leaf r

infixl 9 |>
(|>) : FTCQueue m a x -> (x -> m b) -> FTCQueue m a b
t |> r = Node t (Leaf r)

infixl 9 ><
(><) : FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b
t1 >< t2 = Node t1 t2

infixl 9 :|
data ViewL : (m : Type -> Type) -> a -> b -> Type where
  TOne  : (a -> m b) -> ViewL m a b
  (:|)  : (a -> m x) -> (FTCQueue m x b) -> ViewL m a b

tviewl : FTCQueue m a b -> ViewL m a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go : FTCQueue m a x -> FTCQueue m x b -> ViewL m a b
   go (Leaf r) tr = r :| tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
