module Dijkstra

-- Based on https://www.fstar-lang.org/papers/dm4free/slides.pdf

data Unit : Type -> Type where
  U : Unit a

STwp : Type -> Type -> Type
STwp s a = s -> (a -> s -> Type) -> Type

ST : (s : Type) -> (a : Type) -> STwp s a -> Type
ST s a p  = (st : s) -> (k : (a -> s -> Type)) -> Unit (p st k) -> Type

returnwp : a -> STwp s a
returnwp v st k = k v st

getwp : () -> STwp s s
getwp () st k = k st st

setwp : s -> STwp s ()
setwp st _ k = k () st

bindwp : STwp s a -> (a -> STwp s b) -> STwp s b
bindwp wp f st k = wp st (\b, st' => f b st' k)

return : (v : a) -> ST s a (returnwp v)
return v st k _ = returnwp v st k

get : ST s s (getwp ())
get st k _ = (getwp ()) st k

set : (st : s) -> ST s () (setwp st)
set st st' k _ = (setwp st) st' k

(>>=) : {wa : STwp s a} -> {wb : a -> STwp s b} ->
        ST s a wa -> ((x : a) -> ST s b (wb x)) -> ST s b (bindwp wa wb)
(>>=) m f st k _ = m st (\v, st' => f v st' k U) U

incr : ST Nat () (\s, post => post () (S s))
incr = do x <- get
          set (S x)

test : incr 0 (\x, s => 1 = s) U
test = Refl
