module Regex

data ListF : Type -> Type -> Type where
  Nil : ListF a f
  Cons : a -> f -> ListF a f

data StdRegF : (r : Type) -> Type where
   NoMatch : StdRegF r
   MatchChar : Char -> StdRegF r
   Or : r -> r -> StdRegF r
   Plus : r -> StdRegF r
   Concat : r -> r -> StdRegF r

data Mu : (f : Type -> Type) -> Type where
  In : (f (Mu f)) -> Mu f

List' : Type -> Type
List' a = Mu (ListF a)

nil : List' a
nil = In Nil

isNil : List' a -> Bool
isNil (In []) = False
isNil (In (Cons x xs)) = True

(::) : a -> List' a -> List' a
(::) x xs = In (Cons x xs)

StdReg : Type
StdReg = Mu StdRegF

McatapnAlg : (f : Type -> Type) -> (x : Type -> Type) -> Type
McatapnAlg f x = {r : Type} -> (r -> x r) -> (r -> Mu f) -> f r -> x r

mcatapn : McatapnAlg f x -> Mu f -> x (Mu f)
mcatapn alg (In d) = alg (mcatapn alg) id d

K : Type -> Type
K t = t -> Bool

MatchT : Type -> Type
MatchT t = K t -> Bool

matchi : {t : Type} -> (t -> StdReg -> MatchT t) -> StdReg -> Char -> t -> MatchT t
matchi {t} match reg = mcatapn {x = MatchiX t} alg reg
  where MatchiX : (t : Type) -> (r : Type) -> Type
        MatchiX t _ = Char -> t -> MatchT t
        alg : McatapnAlg StdRegF (MatchiX t)
        alg eval _ NoMatch c cs k = False
        alg eval _ (MatchChar c') c cs k = if c == c' then k cs else False
        alg eval _ (Or r1 r2) c cs k = eval r1 c cs k || eval r2 c cs k
        alg eval reveal (Plus r) c cs k = eval r c cs (\cs => k cs || match cs (In (Plus $ reveal r)) k)
        alg eval reveal (Concat r1 r2) c cs k = eval r1 c cs (\cs => match cs (reveal r2) k)
  --where

-- matchi match NoMatch c cs k = False
-- matchi match (MatchChar c') c cs k = if c == c' then k cs else False
-- matchi match (Or r1 r2) c cs k = matchi match r1 c cs k || matchi match r2 c cs k
-- matchi match (Plus r) c cs k = matchi match r c cs (\cs => k cs || match cs (Plus r) k)
-- matchi match (Concat r1 r2) c cs k = matchi match r1 c cs (\cs => match cs r2 k)
--
-- matchh : List Char -> StdReg -> MatchT
-- matchh [] r k = False
-- matchh (c :: cs) r k = matchi matchh r c cs k
--


match : List' Char -> StdReg -> Bool
match xs reg = mcatapn alg xs reg isNil
  where MatchX : Type -> Type
        MatchX r = StdReg -> MatchT r
        alg : McatapnAlg (ListF Char) MatchX
        alg eval _ Nil r k = False
        alg eval _ (Cons c cs) r k = matchi eval r c cs k
