module FTCQueue

-- Based on http://okmij.org/ftp/Haskell/extensible/FTCQueue.hs

data Tree : (r : Type -> Type -> Type) -> (Type -> Type -> Type) where
  Leaf : r a b -> Tree r a b
  Node : Tree r a x -> Tree r x b -> Tree r a b

data FTCQueue : (r : Type -> Type -> Type) -> (Type -> Type -> Type) where
  Empty : FTCQueue r a a
  Filled : Tree r a b -> FTCQueue r a b

tempty : FTCQueue r a a
tempty = Empty

tsingleton : r a b -> FTCQueue r a b
tsingleton r = Filled (Leaf r)

infixl 9 |>
(|>) : FTCQueue r a x -> r x b -> FTCQueue r a b
Empty |> r = Filled (Leaf r)
(Filled t) |> r = Filled (Node t (Leaf r))

infixl 9 ><
(><) : FTCQueue r a x -> FTCQueue r x b -> FTCQueue r a b
Empty >< t2 = t2
t1 >< Empty = t1
(Filled t1) >< (Filled t2) = Filled (Node t1 t2)

infixl 9 :|
data ViewL : (r : Type -> Type -> Type) -> (Type -> Type -> Type) where
  TEmptyL : ViewL r a a
  (:|)    : r a x -> FTCQueue r x b -> ViewL r a b

tviewl : FTCQueue r a b -> ViewL r a b
tviewl Empty = TEmptyL
tviewl (Filled (Leaf r)) = r :| Empty
tviewl (Filled (Node t1 t2)) = go t1 t2
 where
   go : Tree r a x -> Tree r x b -> ViewL r a b
   go (Leaf r) tr = r :| Filled tr
   go (Node tl1 tl2) tr = go tl1 (Node tl2 tr)
