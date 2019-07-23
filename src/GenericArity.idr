module GenericArity

-- Inspired by https://strathprints.strath.ac.uk/68800/

import Data.Vect

Types : Nat -> Type
Types n = Vect n Type

Arrows : (n : Nat) -> Types n -> Type -> Type
Arrows Z [] b = b
Arrows (S n) (a :: as) b = a -> Arrows n as b

Product : (n : Nat) -> Types n -> Type
Product Z [] = ()
Product (S n) (a :: as) = (a, Product n as)


curryn : (n : Nat) -> {as : Types n} -> (Product n as -> r) -> Arrows n as r
curryn Z {as = []} f = f ()
curryn (S n) {as = (a :: as)} f = curryn n . curry f

uncurryn : (n : Nat) -> {as : Types n} -> Arrows n as r -> (Product n as -> r)
uncurryn Z {as = []} f () = f
uncurryn (S n) {as = (a :: as)} f (x, prod) = uncurryn n (f x) prod

Cong : (n : Nat) -> {as : Types n} -> Arrows n as r -> Arrows n as r -> Type
Cong Z {as = []} f g = f = g
Cong (S n) {as = (a :: as)} f g = {x, y : a} -> x = y -> Cong n (f x) (g y)

congn : (n : Nat) -> {as : Types n} -> {r : Type} -> (f : Arrows n as r) -> Cong n {as} f f
congn Z {as = []} f = Refl
congn (S n) {as = (a :: as)} f = \(Refl {x}) => congn n {as} (f x)

cong : {a, b : Type} -> {f : a -> b} -> {x, y : a} -> x = y -> f x = f y
cong {a} {b} {f} = let r = congn 1 {as = (a :: [])} {r = b} f in r

testCong : (f : Int -> String -> Bool) -> f 1 "1" = f 1 "1"
testCong f = let r = congn 2 {as = (Int :: String :: [])} {r = Bool} f in r Refl Refl

Subst : (n : Nat) -> {as : Types n} -> Arrows n as Type -> Arrows n as Type -> Type
Subst Z {as = []} p q = p -> q
Subst (S n) {as = (a :: as)} p q = {x, y : a} -> x = y -> Subst n (p x) (p y)

substn : (n : Nat) -> {as : Types n} -> (p : Arrows n as Type) -> Subst n {as} p p
substn Z {as = []} p = id
substn (S n) {as = (a :: as)} p = \(Refl {x}) => substn n {as} (p x)

subst : {a : Type} -> (p : a -> Type) -> {x, y : a} -> x = y -> p x -> p y
subst {a} p = let r = substn 1 {as = (a :: [])} p in r

testSubst : (p : Int -> String -> Type) -> p 1 "1" -> p 1 "1"
testSubst p = let r = substn 2 {as = (Int :: String :: [])} p in r Refl Refl
