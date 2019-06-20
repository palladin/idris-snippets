module FreeSelectiveDelivery

-- Based on https://www.staff.ncl.ac.uk/andrey.mokhov/selective-functors.pdf,
--          https://www.cs.ox.ac.uk/jeremy.gibbons/publications/delivery.pdf

interface Applicative f => Selective (f : Type -> Type) where
  select : f (Either a b) -> f (a -> b) -> f b

data Select : (Type -> Type) -> Type -> Type where
  Pure : a -> Select f a
  SelectC : Select f (Either a b) -> f (a -> b) -> Select f b


Functor f => Functor (Select f) where
  map f (Pure x) = Pure $ f x
  map f (SelectC fe ff) = SelectC (map (map f) fe) (map (f .) ff)


Functor f => Applicative (Select f) where
  pure x = Pure x

  (Pure f) <*> fa = map f fa
  (SelectC fe ff) <*> fa = SelectC (pure (\e, a => either (\x => Left (x, a)) (\f => Right (f a)) e) <*> fe <*> fa)
                                   (map uncurry ff)


Functor f => Selective (Select f) where
  select fe (Pure f) = map (either f id) fe
  select fe (SelectC fe' ff') = SelectC (select (map f fe) (map g fe')) (map uncurry ff')
    where
      f : {a, a', b : Type} -> Either a b -> Either a (Either (a', a) b)
      f e = map Right e
      g : {a, a', b : Type} -> Either a' (a -> b) -> a -> Either (a', a) b
      g e a = either (\a' => Left (a', a)) (\f => Right $ f a) e
