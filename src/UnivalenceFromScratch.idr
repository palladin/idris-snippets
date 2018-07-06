module UnivalenceFromScratch

-- Based on http://www.cs.bham.ac.uk/~mhe/agda-new/UnivalenceFromScratch.html

data Sigma : (x : Type) -> (y : x -> Type) -> Type where
  Pair : (a : x) -> y a -> Sigma x y

-- We need something like --without-K
data Id : {x : Type} -> x -> x -> Type where
  Refl : (a : x) -> Id a a

J : {x : Type} ->
    (alpha : (a, b : x) -> Id a b -> Type) ->
    ((a : x) -> alpha a a (Refl a)) ->
    (a, b : x) -> (p : Id a b) -> alpha a b p
J alpha f b b (Refl b) = f b

isSingleton : Type -> Type
isSingleton x = Sigma x (\a => (b : x) -> Id a b)

fiber : {x, y : Type} -> (x -> y) -> y -> Type
fiber {x} f b = Sigma x (\a => Id (f a) b)

isEquiv : {x, y : Type} -> (x -> y) -> Type
isEquiv {y} f = (b : y) -> isSingleton (fiber f b)

Eq : Type -> Type -> Type
Eq x y = Sigma (x -> y) (\f => isEquiv f)

singletonType : {x : Type} -> x -> Type
singletonType {x} a = Sigma x (\b => Id b a)

eta : {x : Type} -> (a : x) -> singletonType a
eta a = Pair a (Refl a)

singletonTypesAreSingletons : {x : Type} -> (a : x) -> isSingleton (singletonType a)
singletonTypesAreSingletons = h
  where
    alpha : (b, a : x) -> Id b a -> Type
    alpha b a p = Id (eta a) (Pair b p)
    f : (a : x) -> alpha a a (Refl a)
    f a = Refl (eta a)
    phi : (b, a : x) -> (p : Id b a) -> Id (eta a) (Pair b p)
    phi = J alpha f
    g : (a : x) -> (sigma : singletonType a) -> Id (eta a) sigma
    g a (Pair b p) = phi b a p
    h : (a : x) -> Sigma (singletonType a) (\b => (sigma : singletonType a) -> Id b sigma)
    h a = Pair (eta a) (g a)

id : (x : Type) -> x -> x
id x a = a

idIsEquiv : (x : Type) -> isEquiv (id x)
idIsEquiv x = g
 where
  g : (a : x) -> isSingleton (fiber (id x) a)
  g = singletonTypesAreSingletons

idToEq : (x, y : Type) -> Id x y -> Eq x y
idToEq = J alpha f
  where
    alpha : (x, y : Type) -> Id x y -> Type
    alpha x y p = Eq x y
    f : (x : Type) -> alpha x x (Refl x)
    f x = Pair (id x) (idIsEquiv x)

isUnivalent : Type
isUnivalent = (x, y : Type) -> isEquiv (idToEq x y)
