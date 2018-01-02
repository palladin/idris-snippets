module Eff

-- The Eff monad, based on http://okmij.org/ftp/Haskell/extensible/more.pdf

data Exists : List a -> a -> Type where
    Here : Exists (x :: xs) x
    There : Exists xs x -> Exists (y :: xs) x

data Eff : List (Type -> Type) -> Type -> Type where
  Pure : a -> Eff xs a
  Bind : {e : Exists xs f} -> f a -> (a -> Eff xs b) -> Eff xs b


(>>=) : Eff xs a -> (a -> Eff xs b) -> Eff xs b
(>>=) (Pure x) f = f x
(>>=) (Bind {e} x g) f = Bind {e} x (\a => (g a) >>= f)

-- State effect
data State : (s : Type) -> Type -> Type where
  Get : State s s
  Put : s -> State s ()

get : {auto e : Exists xs (State s)} -> Eff xs s
get {e} = Bind {e} Get Pure

put : {auto e : Exists xs (State s)} -> s -> Eff xs ()
put {e} s = Bind {e} (Put s) Pure

-- Reader effect
data Reader : (e : Type) -> Type -> Type where
  Ask : Reader e e

ask : {auto e : Exists xs (Reader en)} -> Eff xs en
ask {e} = Bind {e} Ask Pure

-- Interpreters
runState : s -> Eff ((State s) :: xs) a -> Eff xs (a, s)
runState s (Pure x) = Pure (x, s)
runState s (Bind {e = Here} Get f) = runState s (f s)
runState s (Bind {e = Here} (Put s') f) = runState s' (f ())
runState s (Bind {e = (There e')} fa f) = Bind {e = e'} fa (\x => runState s (f x))

runReader : en -> Eff ((Reader en) :: xs) a -> Eff xs a
runReader en (Pure x) = Pure x
runReader en (Bind {e = Here} Ask f) = runReader en (f en)
runReader en (Bind {e = (There e')} fa f) = Bind {e = e'} fa (\x => runReader en (f x))

run : Eff [] a -> a
run (Pure x) = x
run (Bind {e = Here} _ _) impossible
run (Bind {e = (There _)} _ _) impossible

--
example : Eff [State Int, Reader Int] Int
example = do s <- get
             put (s + 1)
             s <- get
             a <- ask
             Pure (s + a)

test : Int
test = (fst . run . runReader 1 . runState 0) example
