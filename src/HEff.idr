module HEff

-- Based on https://github.com/effectfully/Eff/blob/master/Resources/Core.agda

import Data.HVect

Effect : Type -> Type
Effect r = r -> (a : Type) -> (a -> r) -> Type

Effects : (Type -> Type) -> Vect n Type -> Vect n Type
Effects f [] = []
Effects f (x :: xs) = f x :: Effects f xs

HEffect : Type
HEffect = {n : Nat} -> {rs : Vect n Type} -> HVect (Effects Effect rs) -> Effect (HVect rs)

data Exists : {rs : Vect n Type} -> HVect rs -> Type -> Type where
  Here : Exists (x :: xs) x
  There : Exists xs x -> Exists (y :: xs) x

update' : {rs : Vect n Type} -> HVect rs -> (i : Fin n) -> index i rs -> HVect rs
update' [] FZ _ impossible
update' [] (FS _) _ impossible
update' (x :: xs) FZ v = v :: xs
update' (x :: xs) (FS i) v = x :: update' xs i v

data HEff : HEffect where
  Pure : (x : a) -> HEff xs (r' x) a r'
  Bind : {rs : Vect n Type} -> (i : Fin n) -> (eff : Effect (index i rs)) ->
          eff s a s' ->
          ((x : a) -> HEff xs (update' {rs = rs} r i (s' x)) b r'') -> HEff xs r b r''


(>>=) : HEff xs r a r' -> ((x : a) -> HEff xs (r' x) b r'') -> HEff xs r b r''
(>>=) (Pure x) f = f x
(>>=) (Bind i eff x f) g = Bind i eff x (\y => f y >>= g)

data Access = LoggedOut | LoggedIn
data LoginResult = OK | BadPassword
data Store : Access -> (ty : Type) -> (ty -> Access) -> Type where
  Login : Store LoggedOut LoginResult (\res => case res of
                                                  OK => LoggedIn
                                                  BadPassword => LoggedOut)

  Logout : Store LoggedIn () (const LoggedOut)


logout : HEff xs r () r'

test : HEff {rs = [Access]} [Store] [LoggedIn] () (\x => [LoggedOut])
