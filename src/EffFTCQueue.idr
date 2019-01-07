module EffFTCQueue

import src.FTCQueue
import Data.Morphisms


data Exists : List a -> a -> Type where
    Here : Exists (x :: xs) x
    There : Exists xs x -> Exists (y :: xs) x

data Eff : List (Type -> Type) -> Type -> Type where
  Pure : a -> Eff xs a
  Bind : {e : Exists xs f} -> f a -> FTCQueue (Kleislimorphism (Eff xs)) a b -> Eff xs b


(>>=) : Eff xs a -> (a -> Eff xs b) -> Eff xs b
(>>=) (Pure x) f = f x
(>>=) (Bind {e} x g) f = Bind {e} x (g |> (Kleisli f))

-- Reader effect
data Reader : (e : Type) -> Type -> Type where
  Ask : Reader e e

ask : {auto e : Exists xs (Reader en)} -> Eff xs en
ask {e} = Bind {e} Ask (tsingleton (Kleisli Pure))

qApp : FTCQueue (Kleislimorphism (Eff r)) b w -> b -> Eff r w
qApp q x with (tviewl q)
  qApp q x | (TOne (Kleisli k)) = k x
  qApp q x | ((Kleisli k) :| w) with (k x)
    qApp q x | ((Kleisli k) :| w) | (Pure y) = qApp w y
    qApp q x | ((Kleisli k) :| w) | (Bind {e} y z) = Bind {e} y (z >< w)

qComp : FTCQueue (Kleislimorphism (Eff r)) a b -> (Eff r b -> Eff r' c) -> Kleislimorphism (Eff r') a c
qComp g h = Kleisli (\a => (h . qApp g) a)

runReader : en -> Eff ((Reader en) :: xs) a -> Eff xs a
runReader en (Pure x) = Pure x
runReader en (Bind {e = Here} Ask f) = runReader en (qApp f en)
runReader en (Bind {e = (There e')} fa f) = Bind {e = e'} fa  (tsingleton (qComp f (runReader en)))

run : Eff [] a -> a
run (Pure x) = x
run (Bind {e = Here} _ _) impossible
run (Bind {e = (There _)} _ _) impossible

example : Eff [Reader Int] Int
example = do a <- ask
             Pure (1 + a)

test : Int
test = (run . runReader 1) example
