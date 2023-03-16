module Regex

-- Based on https://www.cs.purdue.edu/homes/bendy/CoqSubsidiary/dc-recursion.pdf

data ListF : Type -> Type -> Type where
  Nil : ListF a f
  Cons : a -> f -> ListF a f

data Regex : Type where
   NoMatch : Regex
   MatchChar : Char -> Regex
   Or : Regex -> Regex -> Regex
   Plus : Regex -> Regex
   Concat : Regex -> Regex -> Regex

Functor (ListF a) where
  map f [] = []
  map f (Cons x y) = Cons x (f y)


data Mu : (f : Type -> Type) -> Type where
  In : (r : Type) -> (r -> Mu f) -> f r -> Mu f

inMu : f (Mu f) -> Mu f
inMu d = In (Mu f) id d

outMu : Functor f => Mu f -> f (Mu f)
outMu (In _ f d) = map f d

KAlg : Type
KAlg = (Type -> Type) -> Type

FoldT : KAlg -> Type -> Type
FoldT a r = (x : Type -> Type) -> Functor x -> a x -> r -> x r

AlgF : (Type -> Type) -> (Type -> Type) -> Type
AlgF f x = (r : Type) -> (r -> x r) -> f r -> x r

data DcF : (Type -> Type) -> Type -> Type where
  InDcF : ((x : Type -> Type) -> Functor x -> AlgF f x -> x c) -> DcF f c

Functor (DcF f) where
  map f (InDcF g) = InDcF (\x, fun, alg => map f (g x fun alg))

Dc : (Type -> Type) -> Type
Dc f = Mu (DcF f)

rollDc : DcF f (Dc f) -> Dc f
rollDc = inMu

unrollDc : Dc f -> DcF f (Dc f)
unrollDc = outMu

fold : FoldT (AlgF f) (Dc f)
fold = \x, fun, alg, d => let (InDcF g) = unrollDc d in g x fun alg

inDc : f (Dc f) -> Dc f
inDc d = rollDc $ InDcF (\x, fun, alg => alg (Mu (DcF f)) (fold {f = f} x fun alg) d)

listFold : List a -> (ListF a x -> x) -> x
listFold [] alg = alg Nil
listFold (x :: xs) alg = alg (Cons x (listFold xs alg))

str : String -> Dc (ListF Char)
str xs = listFold (unpack xs) alg
  where
    alg : ListF Char (Mu (DcF (ListF Char))) -> Mu (DcF (ListF Char))
    alg [] = inDc []
    alg (Cons x y) = inDc (Cons x y)

char : Char -> Regex
char c = MatchChar c

concat : Regex -> Regex -> Regex
concat r1 r2 = Concat r1 r2

or : Regex -> Regex -> Regex
or r1 r2 = Or r1 r2

plus : Regex -> Regex
plus r = Plus r

K : Type -> Type
K t = t -> Bool

MatchT : Type -> Type
MatchT t = K t -> Bool


data MatchX : Type -> Type where
  InMatchX : (Regex -> MatchT r) -> MatchX r

outMatchX : MatchX r -> Regex -> MatchT r
outMatchX (InMatchX f) = f

[const] Functor MatchX where
  map f fa = InMatchX $ \regex, k => outMatchX fa regex (\x => k $ f x)

matchi : {t : Type} -> (t -> MatchX t) -> Regex -> Char -> t -> MatchT t
matchi {t} match NoMatch c cs k = False
matchi {t} match (MatchChar c') c cs k = if c == c' then k cs else False
matchi {t} match (Or r1 r2) c cs k = matchi match r1 c cs k || matchi match r2 c cs k
matchi {t} match (Plus r) c cs k = matchi match r c cs (\cs =>  k cs || (let matchX = outMatchX $ match cs in matchX (Plus r) k))
matchi {t} match (Concat r1 r2) c cs k = matchi match r1 c cs (\cs => let matchX = outMatchX $ match cs in matchX r2 k)

match : AlgF (ListF Char) MatchX
match _ rec Nil = InMatchX (\reg, k => False)
match _ rec (Cons c cs) = InMatchX (\reg, k => matchi rec reg c cs k)

foldMatch : Dc (ListF Char) -> Regex -> Bool
foldMatch xs reg =
  let matchX = outMatchX $ fold {f = ListF Char} MatchX const match xs in
  matchX reg (\_ => True)


example : Regex
example = concat (concat (char 'c') (plus $ or (char 'a') (char 'd'))) (char 'r')

test0 : foldMatch (str "car") Regex.example = True
test0 = Refl

test1 : foldMatch (str "cdr") Regex.example = True
test1 = Refl

test2 : foldMatch (str "cr") Regex.example = False
test2 = Refl

test3 : foldMatch (str "cddar") Regex.example = True
test3 = Refl

test4 : foldMatch (str "cdda") Regex.example = False
test4 = Refl
