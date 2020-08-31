module Regex

-- Based on https://homepage.divms.uiowa.edu/~astump/papers/stump-icfp20.pdf

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

str : String -> List' Char
str xs = str' $ unpack xs
  where str' : List Char -> List' Char
        str' [] = In $ Nil
        str' (x :: xs) = In $ Cons x (str' xs)

StdReg : Type
StdReg = Mu StdRegF

char : Char -> StdReg
char c = In $ MatchChar c

concat : StdReg -> StdReg -> StdReg
concat r1 r2 = In $ Concat r1 r2

or : StdReg -> StdReg -> StdReg
or r1 r2 = In $ Or r1 r2

plus : StdReg -> StdReg
plus r = In $ Plus r

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


match : List' Char -> StdReg -> Bool
match xs reg = mcatapn alg xs reg (\_ => True)
  where MatchX : Type -> Type
        MatchX r = StdReg -> MatchT r
        alg : McatapnAlg (ListF Char) MatchX
        alg eval _ Nil r k = False
        alg eval _ (Cons c cs) r k = matchi eval r c cs k

example : StdReg
example = concat (concat (char 'c') (plus $ or (char 'a') (char 'd'))) (char 'r')

test0 : Bool
test0 = match (str "car") example

test1 : Bool
test1 = match (str "cdr") example

test2 : Bool
test2 = match (str "cr") example

test3 : Bool
test3 = match (str "cddar") example

test4 : Bool
test4 = match (str "cdda") example
