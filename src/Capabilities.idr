module Capabilities

-- Inspired by http://okmij.org/ftp/Computation/lightweight-static-guarantees.html

interface Sortable (f : Type -> Type) where
  Sorted : (a : Type) -> (a -> a -> Ordering) -> Type

  sortBy : (cmp : a -> a -> Ordering) -> f a -> Sorted a cmp
  mergeBy : (cmp : a -> a -> Ordering) -> Sorted a cmp  -> Sorted a cmp -> Sorted a cmp
  get : Sorted a cmp -> f a


data Test' : (a : Type) -> (a -> a -> Ordering) -> Type where
   C' : (f : (a -> a -> Ordering)) -> Test' a f

Sortable List where
  Sorted a cmp = List a

  sortBy cmp xs = List.sortBy cmp xs
  mergeBy cmp xs ys = List.mergeBy cmp xs ys
  get xs = xs


example : Sortable f => (cmp : a -> a -> Ordering) -> f a -> f a -> f a
example @{sortable} cmp xs ys =
  let sxs = sortBy cmp xs in
  let sys = sortBy cmp ys in
  let sms = mergeBy @{sortable} cmp sxs sys in
  get sms
