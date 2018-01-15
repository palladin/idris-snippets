module DatatypeGeneric

data Data : Type where
  Unit : Data
  Zero : Data
  Param : Data
  Rec : Data
  Sum : Data -> Data -> Data
  Prod : Data -> Data -> Data

interp : Data -> Type -> Type -> Type
interp Unit param rec = ()
interp Zero param rec = Void
interp Param param rec = param
interp Rec param rec = rec
interp (Sum x y) param rec = Either (interp x param rec) (interp y param rec)
interp (Prod x y) param rec = (interp x param rec, interp y param rec)

data Mu : (dataF : Data) -> (a : Type) -> Type where
  In : interp dataF a (Mu dataF a) -> Mu dataF a

bimap : (dataF : Data) -> (f : a -> b) -> (g : c -> d) -> interp dataF a c -> interp dataF b d
bimap Unit f g () = ()
bimap Param f g a = f a
bimap Rec f g c = g c
bimap (Sum x y) f g (Left l) = Left (bimap x f g l)
bimap (Sum x y) f g (Right r) = Right (bimap y f g r)
bimap (Prod x y) f g (a, b) = (bimap x f g a, bimap y f g b)

interface Representable (f : Type -> Type) where
  rep : Data
  fromRep : Mu rep a -> f a
  toRep : f a -> Mu rep a

Representable List where
  rep = Sum Unit (Prod Param Rec)

  fromRep (In (Left ())) = []
  fromRep (In (Right (a, b))) = a :: fromRep b

  toRep [] = In (Left ())
  toRep (x :: xs) = In (Right (x, toRep xs))

gmap : {dataF : Data} -> (a -> b) -> Mu dataF a -> Mu dataF b
gmap {dataF = dataF} f (In x) = In $ bimap dataF f (gmap f) x

gcata : {dataF : Data} -> (interp dataF a c -> c) -> Mu dataF a -> c
gcata {dataF = dataF} f (In x) = f $ bimap dataF id (gcata f) x

map' : Representable f => (a -> b) -> f a -> f b
map' f fa = fromRep $ gmap f (toRep fa)

test : List Int
test = map' (\x => x + 1) [1..10]
