module FreerCont

-- Based on https://github.com/lambdageek/freer-church

data FreerCont : (f : Type -> Type) -> Type -> Type where
  Cont : ({r : Type} -> (a -> r) -> ({x : Type} -> f x -> (x -> r) -> r) -> r) -> FreerCont f a

pure : a -> FreerCont f a
pure x = Cont (\k, _ => k x)

(>>=) : FreerCont f a -> (a -> FreerCont f b) -> FreerCont f b
(>>=) (Cont g) f = Cont (\k, imp => g (\x => let (Cont g') = f x in g' k imp) imp)

-- State effect
data State : (s : Type) -> Type -> Type where
  Get : State s s
  Put : s -> State s ()

get : FreerCont (State s) s
get = Cont (\k, imp => imp Get k)

put : s -> FreerCont (State s) ()
put s = Cont (\k, imp => imp (Put s) k)

imp : State s x -> (x -> s -> (s, a)) -> s -> (s, a)
imp Get k st = k st st
imp (Put x) k st = k () x

runState : FreerCont (State s) a -> s -> (s, a)
runState (Cont f) = f k imp
  where
    k : a -> s -> (s, a)
    k x st = (st, x)


example : FreerCont (State Int) Int
example = do s <- get
             put (s + 1)
             s <- get
             pure (s + 1)

test : (Int, Int)
test = runState example 0
