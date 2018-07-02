module Dijkstra

-- Based on https://www.fstar-lang.org/papers/dm4free/slides.pdf

STwp : Type -> Type -> Type
STwp s a = s -> (a -> s -> Type) -> Type

ST : (s : Type) -> (a : Type) -> STwp s a -> Type
ST s a p  = (st : s) -> (k : (a -> s -> Type)) -> p st k -> Type

returnwp : a -> STwp s a
returnwp v st p = p v st

getwp : () -> STwp s s
getwp () st p = p st st

setwp : s -> STwp s ()
setwp st _ p = p () st

bindwp : STwp s a -> (a -> STwp s b) -> STwp s b
bindwp wp f st p = wp st (\b, st' => f b st' p)

return : (v : a) -> ST s a (returnwp v)
return v st _ _ = ()

get : ST s s (getwp ())
get st _ _ = ()

set : (st : s) -> ST s () (setwp st)
set st st' _ _ = ()

(>>=) : {wa : STwp s a} -> {wb : a -> STwp s b} ->
        ST s a wa -> ((x : a) -> ST s b (wb x)) -> ST s b (bindwp wa wb)
(>>=) {wa} {wb} m f st p wp = ()

example : ST Nat () (\s, post => post () (S s))
example = do x <- get
             set (S x)

test : Type
test = example 0 (\x, s => 1 = s) Refl
