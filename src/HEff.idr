module HEff

-- Based on https://github.com/effectfully/Eff/blob/master/Resources/Core.agda

import Data.HVect

Effect : Type -> Type
Effect r = r -> (a : Type) -> (a -> r) -> Type

Effects : (Type -> Type) -> Vect n Type -> Vect n Type
Effects f [] = []
Effects f (x :: xs) = f x :: Effects f xs

data Exists' : {t : Type} -> {rs : Vect n Type} ->
               HVect rs -> t -> HVect (Effects Effect rs) -> Effect t -> Type where
  Here : Exists' (x :: xs) x (y :: ys) y
  There : Exists' xs x ys y -> Exists' (_ :: xs) x (_ :: ys) y

update' : {t : Type} -> (r : HVect rs) -> (e : Exists' {t = t} r s effs eff) -> t -> HVect rs
update' [] Here _ impossible
update' [] (There _) _ impossible
update' (x :: xs) Here v = v :: xs
update' (x :: xs) (There e) v = x :: update' xs e v

HEffect : Type
HEffect = {n : Nat} -> (rs : Vect n Type) -> HVect (Effects Effect rs) -> Effect (HVect rs)

data HEff : HEffect where
  Pure : (x : a) -> HEff rs effs (r' x) a r'
  Bind : (e : Exists' r s effs eff) ->
          eff s a s' ->
          ((x : a) -> HEff rs effs (update' r e (s' x)) b r'') -> HEff rs effs r b r''

(>>=) : HEff rs effs r a r' -> ((x : a) -> HEff rs effs (r' x) b r'') -> HEff rs effs r b r''
(>>=) (Pure x) f = f x
(>>=) (Bind e x f) g = Bind e x (\y => f y >>= g)

data Access = LoggedOut | LoggedIn
data Store : Access -> (ty : Type) -> (ty -> Access) -> Type where
  Login : Store LoggedOut () (const LoggedIn)
  Logout : Store LoggedIn () (const LoggedOut)

login : {auto e : Exists' r LoggedOut effs Store} ->
         HEff rs effs r () (\_ => update' r e LoggedIn)
login {e} = Bind e Login Pure

logout : {auto e : Exists' r LoggedIn effs Store} ->
         HEff rs effs r () (\_ => update' r e LoggedOut)
logout {e} = Bind e Logout Pure

data State : Type -> (a : Type) -> (a -> Type) -> Type where
  Get : State s s (const s)
  Put : s' -> State s () (const s')

get : {auto e : Exists' r s effs State} ->
      HEff rs effs r s (\_ => update' r e s)
get {e} = Bind e Get Pure

put : {auto e : Exists' r s effs State} -> s' ->
      HEff rs effs r () (\_ => update' r e s')
put {e} s' = Bind  e (Put s') Pure

run : HEff [] [] r a r' -> a
run (Pure x) = x
run (Bind Here _ _) impossible
run (Bind (There _) _ _) impossible

head' : HVect xs -> head xs
head' (x :: _) = x
tail' : HVect xs -> HVect (tail xs)
tail' (x :: xs) = xs

runStore : HEff (Access :: rs) (Store :: effs) r a r' -> HEff rs effs (tail' r) a (\x => tail' $ r' x)
runStore (Pure x) = Pure x
runStore (Bind Here Login f) = runStore $ f ()
runStore (Bind Here Logout f) = runStore $ f ()
runStore (Bind (There e) eff f) = Bind e eff (\x => runStore $ f x)

runState : (head' r) -> HEff (Type :: rs) (State :: effs) r a r' ->  HEff rs effs (tail' r) (DPair a (\x => head' $ r' x)) (\x => tail' $ r' (fst x))
runState s (Pure x) = Pure (x ** s)
runState s (Bind Here Get f) = runState s $ f s
runState s (Bind Here (Put s') f) = runState s' $ f ()
runState s (Bind (There e) eff f) = Bind e eff (\x => runState s $ f x)

example : HEff [Access, Type] [Store, State] [LoggedOut, Nat] Nat (\n => [LoggedOut, Vect n Bool])
example = do login
             n <- get
             put (replicate n True)
             logout
             Pure n

test : DPair Nat (\n => Vect n Bool)
test = run . runState 3 . runStore $ example 
