module FTCQueue

-- Based on http://okmij.org/ftp/Haskell/AlgorithmsH1.html#FTCQueue
%access public export

data FTCQueue : (r : Type -> Type -> Type) -> Type -> Type -> Type where
  Leaf : r a b -> FTCQueue r a b
  Node : FTCQueue r a x -> FTCQueue r x b -> FTCQueue r a b

tsingleton : r a b -> FTCQueue r a b
tsingleton r = Leaf r

infixl 9 |>
(|>) : FTCQueue r a x -> r x b -> FTCQueue r a b
t |> r = Node t (Leaf r)

infixl 9 ><
(><) : FTCQueue r a x -> FTCQueue r x b -> FTCQueue r a b
t1 >< t2 = Node t1 t2

infixl 9 :|
data ViewL : (r : Type -> Type -> Type) -> Type -> Type -> Type where
  TOne  : r a b -> ViewL r a b
  (:|)  : r a x -> FTCQueue r x b -> ViewL r a b

tviewl : FTCQueue r a b -> ViewL r a b
tviewl (Leaf r) = TOne r
tviewl (Node t1 t2) = go t1 t2
 where
   go : FTCQueue r a x -> FTCQueue r x b -> ViewL r a b
   go (Leaf r) tr = r :| tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
