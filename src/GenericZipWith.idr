module GenericZipWith

import Data.Vect

Id : Type -> Type
Id x = x

Func : (args : Vect n Type) -> (ret : Type) -> (Type -> Type) -> Type
Func [] r f = f r
Func (x :: xs) r f = (a : f x) -> Func xs r f

gApp : Applicative f => f (Func v r Id) -> Func v r f
gApp {v = []} fs = fs
gApp {v = (x :: xs)} fs = \vs => gApp (fs <*> vs)

gZipWith : Applicative f => Func v r Id -> Func v r f
gZipWith {f} f' = gApp {f = f} (pure f')

zipWith' : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith' f = gZipWith {v = [a, b]} f

zipWith3' : (a -> b -> c -> d) -> Vect n a -> Vect n b -> Vect n c -> Vect n d
zipWith3' f = gZipWith {v = [a, b, c]} f

map' : (a -> b) -> Vect n a -> Vect n b
map' f = gZipWith {v = [a]} f

repeat' : b -> Vect n b
repeat' b = gZipWith {v = []} b

example : Vect 2 (Int, Bool)
example = zipWith' (\i, b => (i, b)) [1, 2] [True, False]
