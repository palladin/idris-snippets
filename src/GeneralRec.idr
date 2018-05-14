module GeneralRec

-- https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf
-- http://okmij.org/ftp/Haskell/extensible/more.pdf

data Freer : (f : Type -> Type) -> Type -> Type where
  Pure : a -> Freer f a
  Bind : f a -> (a -> Freer f b) -> Freer f b

(>>=) : Freer f a -> (a -> Freer f b) -> Freer f b
(>>=) (Pure x) f = f x
(>>=) (Bind x g) f = Bind x (\a => g a >>= f)


data General : (f : a -> Type) -> Type -> Type where
  Rec : (x : a) -> General f (f x)

PiG : (s : Type) -> (f : s -> Type) -> Type
PiG s f = (x : s) -> Freer (General f) (f x)

call : (x : a) -> Freer (General f) (f x)
call x = Bind (Rec x) Pure

runGeneral : {f : a -> Type} -> ((x : a) -> f x) -> Freer (General f) c -> c
runGeneral rec (Pure x) = x
runGeneral rec (Bind (Rec x) k) = runGeneral rec $ k (rec x)

run : {f : a -> Type} -> PiG a f -> (x : a) -> f x
run f x = runGeneral (run f) (f x)

fusc : PiG Nat (\_ => Nat)
fusc Z = Pure Z
fusc (S n) = do fn <- call n
                ffn <- call fn
                Pure $ S ffn

test : Nat
test = run fusc 10
