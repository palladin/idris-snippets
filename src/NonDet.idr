module NonDet

-- Non-determinism, based on http://okmij.org/ftp/tagless-final/nondet-paper.pdf

import Control.Monad.Identity

interface NDet (rep : Type -> Type) (val : Type -> Type) | rep where
  nil : rep a
  cons : val a -> rep a -> rep a
  list : List a -> rep a
  decon : rep a -> (() -> rep a) -> (val a -> rep a -> rep a) -> rep a
  foldr : (val a -> rep a -> rep a) -> rep a -> rep a -> rep a
  fail : rep a
  (||) : rep a -> rep a -> rep a

data Lists : Type -> Type where
  In : List (List a) -> Lists a

NDet Lists Identity where
  nil = In [[]]
  cons (Id y) (In xss) = In $ map (\xs => y :: xs) xss
  list xs = In [xs]
  decon (In xss) onnil oncons = In $ xss >>= (\xs => case xs of
                                                      [] => let (In yss) = onnil () in yss
                                                      h :: t => let (In yss) = oncons (Id h) (In [t]) in yss)

  foldr f seed (In xss) = In $ xss >>= (\xs => let (In yss) = foldr (\x, acc => f (Id x) acc) seed xs in yss)

  fail = In []
  (||) (In xs) (In ys) = In (xs ++ ys)

insert : NDet rep val => val a -> rep a -> rep a
insert x l = cons x l || decon l (\() => fail) (\h, t => cons h (insert x t))

perm : NDet rep val => List a -> rep a
perm xs = foldr (\x, xs => insert x xs) nil (list xs)

test : Lists Int
test = perm [1, 2, 3]
