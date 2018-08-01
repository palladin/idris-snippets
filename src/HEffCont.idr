module HEffCont


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

data HEffect : {n : Nat} -> (rs : Vect n Type) -> HVect (Effects Effect rs) -> Effect (HVect rs) where
  Pure : (x : a) -> HEffect rs effs (r' x) a r'
  EffectC : (e : Exists' r s effs eff) -> eff s a s' -> HEffect rs effs r a (\x => update' r e (s' x))

data HEff : {n : Nat} -> (rs : Vect n Type) -> HVect (Effects Effect rs) -> Effect (HVect rs) where
  Cont : {rs : Vect n Type} -> ({res : Type} -> (a -> res) -> ({x : Type} -> {r : HVect rs} -> {r' : x -> HVect rs} -> HEffect rs effs r x r' -> (x -> res) -> res) -> res) -> HEff rs effs r a r'

pure : (x : a) -> HEff rs effs (r' x) a r'
pure {r'} x = Cont (\k, imp => imp (Pure {r' = r'} x) k)

(>>=) : HEff rs effs r a r' -> ((x : a) -> HEff rs effs (r' x) b r'') -> HEff rs effs r b r''
(>>=) (Cont g) f = Cont (\k, imp => g (\x => let (Cont g') = f x in g' k imp) imp)

data Access = LoggedOut | LoggedIn
data Store : Access -> (ty : Type) -> (ty -> Access) -> Type where
  Login : Store LoggedOut () (const LoggedIn)
  Logout : Store LoggedIn () (const LoggedOut)

login : {auto e : Exists' r LoggedOut effs Store} ->
         HEff rs effs r () (\_ => update' r e LoggedIn)
login {e} = Cont (\k, imp => imp (EffectC e Login) k)

logout : {auto e : Exists' r LoggedIn effs Store} ->
         HEff rs effs r () (\_ => update' r e LoggedOut)
logout {e} = Cont (\k, imp => imp (EffectC e Logout) k)

runPure : HEffect [] [] r a r' -> (a -> res) -> res
runPure (Pure x) k = k x
runPure (EffectC Here _) _ impossible
runPure (EffectC (There _) _) _ impossible

head' : HVect xs -> head xs
head' (x :: _) = x
tail' : HVect xs -> HVect (tail xs)
tail' (x :: xs) = xs

runStore : {rs : Vect n Type} -> (HEffect rs effs (tail' {xs = (Access :: rs)} r) a (\x => tail' {xs = (Access :: rs)} $ r' x) -> (a -> res) -> res) -> HEffect (Access :: rs) (Store :: effs) r a r' -> (a -> res) -> res
runStore k (Pure x) k' = k' x
runStore k (EffectC Here Login) k' = k' ()
runStore k (EffectC Here Logout) k' = k' ()
runStore k (EffectC (There effs) eff) k' = k (EffectC effs eff) k'

run : {rs : Vect n Type} -> HEff rs effs r a r' -> (a -> res) -> ({x : Type} -> {r : HVect rs} -> {r' : x -> HVect rs} -> HEffect rs effs r x r' -> (x -> res) -> res) -> res
run (Cont f) k imp = f k imp

example : HEff [Access] [Store] [LoggedOut] () (\_ => [LoggedOut])
example = do login
             logout

test : ()
test = run example (\_ => ()) (\eff, k => runStore runPure eff k)
