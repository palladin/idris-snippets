module EffCont

data Exists : List a -> a -> Type where
    Here : Exists (x :: xs) x
    There : Exists xs x -> Exists (y :: xs) x

data Effect : List (Type -> Type) -> Type -> Type where
  Pure : a -> Effect xs a
  EffectC : {f : Type -> Type} -> Exists xs f -> f a -> Effect xs a

data Eff : List (Type -> Type) -> Type -> Type where
  Cont : ({r : Type} -> (a -> r) -> ({x : Type} -> Effect xs x -> (x -> r) -> r) -> r) -> Eff xs a

pure : a -> Eff xs a
pure x = Cont (\k, imp => imp (Pure x) k)

(>>=) : Eff xs a -> (a -> Eff xs b) -> Eff xs b
(>>=) (Cont g) f = Cont (\k, imp => g (\x => let (Cont g') = f x in g' k imp) imp)

-- State effect
data State : (s : Type) -> Type -> Type where
  Get : State s s
  Put : s -> State s ()

get : {auto e : Exists xs (State s)} -> Eff xs s
get {e} = Cont (\k, imp => imp (EffectC e Get) k)

put : {auto e : Exists xs (State s)} -> s -> Eff xs ()
put {e} s = Cont (\k, imp => imp (EffectC e (Put s)) k)

-- Reader effect
data Reader : (e : Type) -> Type -> Type where
  Ask : Reader e e

ask : {auto e : Exists xs (Reader en)} -> Eff xs en
ask {e} = Cont (\k, imp => imp (EffectC e Ask) k)

-- Interpreters
runPure : Effect [] x -> (x -> r) -> r
runPure (Pure x) k = k x
runPure (EffectC Here _) _ impossible
runPure (EffectC (There _) _) _ impossible

stateImp : State s x -> (x -> s -> r) -> s -> r
stateImp Get k st = k st st
stateImp (Put st') k st = k () st'

runState : (Effect xs x -> (x -> r) -> r) -> Effect (State s :: xs) x -> (x -> s -> r) -> s -> r
runState k (Pure x) k' = k' x
runState k (EffectC Here effect) k' = stateImp effect k'
runState k (EffectC (There xs) fa) k' = \st => k (EffectC xs fa) (\x => k' x st)

readerImp : Reader e x -> (x -> e -> r) -> e -> r
readerImp Ask k e = k e e

runReader : (Effect xs x -> (x -> r) -> r) -> Effect (Reader e :: xs) x -> (x -> e -> r) -> e -> r
runReader k (Pure x) k' = k' x
runReader k (EffectC Here effect) k' = readerImp effect k'
runReader k (EffectC (There xs) fa) k' = \e => k (EffectC xs fa) (\x => k' x e)

run : (a -> r) -> ({x : Type} -> Effect xs x -> (x -> r) -> r) -> Eff xs a -> r
run k imp (Cont f) = f k imp

example : Eff [State Int, Reader Int] Int
example = do s <- get
             put (s + 1)
             s <- get
             a <- ask
             pure (s + a)

test : (Int, Int, Int)
test = let f = run (\x, s, e => (x, s, e)) (\eff, k => runState (runReader runPure) eff k) example in f 1 2
