module Metamorphic

-- Based on https://bitbucket.org/josh-hs-ko/MetamorphismsInAgda/raw/master/MetamorphismsInAgda.pdf

data AlgList : (a : Type) -> {s : Type} -> (f : a -> s -> s) -> (e : s) -> s -> Type where
  Nil : AlgList a f e e
  (::) : (x : a) -> {st : s} -> AlgList a f e st -> AlgList a f e (f x st)


codata CoAlgList : (b : Type) -> {s : Type} -> (g : s -> Maybe (b, s)) -> s -> Type where
  Empty : {st : s} -> g st = Nothing -> CoAlgList b g st
  Cons : (x : b) -> {st, st' : s} -> g st = Just (x, st') -> CoAlgList b g st' -> CoAlgList b g st


testAlgList : AlgList Nat (\x, s => x + s) 0 3
testAlgList = 1 :: 1 :: 1 :: Nil

testCoAlgList : (st : Nat) -> CoAlgList Nat (\x => Just (x, S x)) st
testCoAlgList st = Cons st Refl (testCoAlgList (S st))

fromLeftAlg : {a, s : Type} -> (s -> a -> s) -> a -> (s -> s) -> (s -> s)
fromLeftAlg f a s = s . flip f a

parameters (a : Type, b : Type, s : Type, f : s -> a -> s, g : s -> Maybe (b, s),
            sc : {x : a} -> {y : b} -> {st, st' : s} -> g st = Just (y, st') -> g (f st x) = Just (y, f st' x))

  cbp : (st : s) -> {h : s -> s} -> AlgList a (fromLeftAlg f) (\x => x) h -> CoAlgList b g (h st)
  cbp s [] with (g s) proof prf
    cbp s [] | Nothing = Empty (sym prf)
    cbp s [] | Just (y, s') = Cons y (sym prf) (cbp s' [])
  cbp s (a :: as) = cbp (f s a) as

  lemma : {st : s} -> {y : b} -> {st' : s} -> {h : s -> s} -> AlgList a (fromLeftAlg f) (\x => x) h -> g st = Just (y, st') -> g (h st) = Just (y, h st')
  lemma [] eq = eq
  lemma (a :: as) eq = lemma as (sc eq)

  stream : (st : s) -> {h : s -> s} -> AlgList a (fromLeftAlg f) (\x => x) h -> CoAlgList b g (h st)
  stream s as with (g s) proof prf
    stream s [] | Nothing  = Empty (sym prf)
    stream s (a :: as) | Nothing  = stream (f s a) as
    stream s as | Just (y, s') = Cons y (lemma as (sym prf)) (stream s' as)
