module RelativeMonad

-- Based on https://www.researchgate.net/publication/286096562_Relative_Monads_Formalised

record Monoid where
  constructor MkMonoid
  S : Type
  e : S
  (.) : S -> S -> S
  lid : (m : S) -> e . m = m
  rid : (m : S) -> m . e = m
  assoc : (m, n, o : S) -> (m . n) . o = m . (n . o)

NatMonoid : Monoid
NatMonoid = MkMonoid
  Nat
  0
  (+)
  (\_ => Refl)
  plusZeroRight
  plussassoc
  where
    plussassoc : (m, n, o : Nat) -> (m + n) + o = m + (n + o)
    plussassoc m n o = sym (plusAssociative m n o)

    plusZeroRight : (m : Nat) -> m + 0 = m
    plusZeroRight m = plusZeroRightNeutral m

record Cat where
  constructor MkCat
  Obj : Type
  Hom : Obj -> Obj -> Type
  iden : (x : Obj) -> Hom x x
  comp : (x, y, z : Obj) -> Hom x y -> Hom y z -> Hom x z
  idl : (x, y : Obj) -> (f : Hom x y) -> comp x x y (iden x) f = f
  idr : (x, y : Obj) -> (f : Hom x y) -> comp x y y f (iden y) = f
  assoc : (w, x, y, z : Obj) -> (f : Hom w x) -> (g : Hom x y) -> (h : Hom y z) ->
            comp w y z (comp w x y f g) h = comp w x z f (comp x y z g h)

identity : (x : Type) -> x -> x
identity _ x = x
compose : (x, y, z : Type) -> (x -> y) -> (y -> z) -> x -> z
compose _ _ _ f g = g . f
idLeft : (x : Type) -> (y : Type) -> (f : x -> y) -> compose x x y (identity x) f = f
idLeft x y f = Refl
idRight : (x : Type) -> (y : Type) -> (f : x -> y) -> compose x y y f (identity y) = f
idRight x y f = Refl
associativity : (w, x, y, z : Type) -> (f : w -> x) -> (g : x -> y) -> (h : y -> z) ->
                  compose w y z (compose w x y f g) h = compose w x z f (compose x y z g h)
associativity w x y z f g h = Refl
TypeMorph : Type -> Type -> Type
TypeMorph a b = a -> b

TypeCat : Cat
TypeCat = MkCat
  Type
  TypeMorph
  identity
  compose
  idLeft
  idRight
  associativity

record Fun (c : Cat) (d : Cat) where
  constructor MkFun
  OMap : Obj c -> Obj d
  HMap : (x, y : Obj c) -> Hom c x y -> Hom d (OMap x) (OMap y)
  fid : (x : Obj c) -> HMap x x (iden c x) = iden d (OMap x)
  fcomp : (x, y, z : Obj c) -> (f : Hom c x y) -> (g : Hom c y z) ->
          HMap x z (comp c x y z f g) = comp d (OMap x) (OMap y) (OMap z) (HMap x y f) (HMap y z g)

listMap : (a : Type) -> (b : Type) -> (a -> b) -> List a -> List b
listMap _ _ f [] = []
listMap _ _ f (x :: xs) = f x :: listMap _ _ f xs

postulate funext : (f, g : a -> b) -> ((x : a) -> f x = g x) -> f = g

listId : (a : Type) -> (xs : List a) -> listMap a a (identity a) xs = identity (List a) xs
listId _ [] = Refl
listId _ (x :: xs) = cong (listId _ xs)

listIdExt : (a : Type) -> listMap a a (identity a) = identity (List a)
listIdExt a = funext (\xs => listMap a a (identity a) xs) (\xs => identity (List a) xs) (listId a)

listComp : (a, b, c : Type) -> (f : a -> b) -> (g : b -> c) ->
          (xs : List a) -> listMap a c (g . f) xs = listMap b c g (listMap a b f xs)
listComp _ _ _ _ _ [] = Refl
listComp _ _ _ _ _ (x :: xs) = cong (listComp _ _ _ _ _ xs)

listCompExt : (a, b, c : Type) -> (f : a -> b) -> (g : b -> c) ->
                listMap a c (g . f) = (\xs => listMap b c g (listMap a b f xs))
listCompExt a b c f g = funext (\xs => listMap a c (g . f) xs)
                               (\xs => listMap b c g (listMap a b f xs))
                               (listComp a b c f g)

ListFunctor : Fun TypeCat TypeCat
ListFunctor = MkFun
  List
  listMap
  listIdExt
  listCompExt

maybeMap : (a : Type) -> (b : Type) -> (a -> b) -> Maybe a -> Maybe b
maybeMap _ _ f Nothing = Nothing
maybeMap _ _ f (Just x) = Just (f x)

maybeId : (a : Type) -> (m : Maybe a) -> maybeMap a a (identity a) m = identity (Maybe a) m
maybeId _ Nothing = Refl
maybeId _ (Just x) = Refl

maybeIdExt : (a : Type) -> maybeMap a a (identity a) = identity (Maybe a)
maybeIdExt a = funext (\m => maybeMap a a (identity a) m ) (\m => identity (Maybe a) m) (maybeId a)

maybeComp : (a, b, c : Type) -> (f : a -> b) -> (g : b -> c) ->
            (m : Maybe a) -> maybeMap a c (\x => g (f x)) m = maybeMap b c g (maybeMap a b f m)
maybeComp = ?fsfs

maybeCompExt : (a, b, c : Type) -> (f : a -> b) -> (g : b -> c) ->
                  maybeMap a c (\x => g (f x)) = (\m => maybeMap b c g (maybeMap a b f m))
maybeCompExt a b c f g = funext (\m => maybeMap a c (\x => g (f x)) m)
                                (\m => maybeMap b c g (maybeMap a b f m))
                                (maybeComp a b c f g)

MaybeFunctor : Fun TypeCat TypeCat
MaybeFunctor = MkFun
  Maybe
  maybeMap
  maybeIdExt
  maybeCompExt

{-
record NatT (c : Cat) (d : Cat) (f : Fun c d) (g : Fun c d) where
  constructor MkNatT
  cmp : {x : Obj c} -> Hom d (OMap f x) (OMap g x)
  nat : {x, y : Obj c} -> {h : Hom c x y} ->
          comp d (HMap g h) cmp = comp d cmp (HMap f h)

MaybeListNat : NatT TypeCat TypeCat MaybeFunctor ListFunctor
MaybeListNat = MkNatT
  cmp
  ?Sfsdf
  where
    cmp : {x : Type} -> Maybe x -> List x
    cmp Nothing = []
    cmp (Just x) = [x]

-}
