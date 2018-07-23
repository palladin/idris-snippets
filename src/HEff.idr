module HEff

-- Based on https://github.com/effectfully/Eff/blob/master/Resources/Core.agda

import Data.HVect

Effect : Type -> Type
Effect r = r -> (a : Type) -> (a -> r) -> Type

Effects : (Type -> Type) -> Vect n Type -> Vect n Type
Effects f [] = []
Effects f (x :: xs) = f x :: Effects f xs

HEffect : Type
HEffect = {n : Nat} -> (rs : Vect n Type) -> HVect (Effects Effect rs) -> Effect (HVect rs)

data Exists' : {t : Type} -> {rs : Vect n Type} ->
               HVect rs -> t -> HVect (Effects Effect rs) -> Effect t -> Type where
  Here : Exists' (x :: xs) x (y :: ys) y
  There : Exists' xs x ys y -> Exists' (_ :: xs) x (_ :: ys) y

update' : {t : Type} -> (r : HVect rs) -> (e : Exists' {t = t} r s effs eff) -> t -> HVect rs
update' [] Here _ impossible
update' [] (There _) _ impossible
update' (x :: xs) Here v = v :: xs
update' (x :: xs) (There e) v = x :: update' xs e v

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

run : HEff [] [] r a r' -> a
run (Pure x) = x
run (Bind Here _ _) impossible
run (Bind (There _) _ _) impossible

tail : HVect xs -> HVect (tail xs)
tail (x :: xs) = xs

runStore : HEff (Access :: rs) (Store :: effs) r a r' -> HEff rs effs (tail r) a (\x => tail $ r' x)
runStore (Pure x) = Pure x
runStore (Bind Here Login f) = runStore $ f ()
runStore (Bind Here Logout f) = runStore $ f ()
runStore (Bind (There e) eff f) = Bind e eff (\x => runStore $ f x)

example : HEff [Access] [Store] [LoggedOut] () (\x => [LoggedOut])
example = do login
             logout

test : ()
test = run . runStore $ example
