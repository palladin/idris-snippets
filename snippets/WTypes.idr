module WTypes

data W : (t : Type) -> (p : t -> Type) -> Type where
  Sup : (x : t) -> (p x -> W t p) -> W t p

ind : {t : Type} -> {p : t -> Type} -> (pred : W t p -> Type) ->
      ((v : t) -> (f : p v -> W t p) -> ((t' : p v) -> pred (f t')) -> pred (Sup v f)) ->
      (w : W t p) -> pred w
ind _ p (Sup x f) = p x f (\t => ind _ p (f t))

efq : {a : Type} -> Void -> a

-- Nat encoding
N : Type
N = W Bool (\b => if b then () else Void)

zero : N
zero = Sup False efq

succ : N -> N
succ n = Sup True (const n)

plus : N -> N -> N
plus (Sup False f) b = b
plus (Sup True f) b = Sup True (\() => plus (f ()) b)

-- Tree encoding
Tree : Type
Tree = W Bool (\b => if b then Bool else Void)

leaf : Tree
leaf = Sup False efq

branch : Tree -> Tree -> Tree
branch l r = Sup True (\b => if b then l else r)

size : Tree -> N
size (Sup False f) = zero
size (Sup True f) = plus (size (f True)) (size (f False))
