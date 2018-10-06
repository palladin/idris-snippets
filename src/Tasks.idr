module Tasks

-- Based on https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems-final.pdf

data Task : (c : (Type -> Type) -> Type) -> Type -> Type -> Type where
  MkTask : ({f : Type -> Type} -> c f -> (k -> f v) -> f v) -> Task c k v

Tasks : ((Type -> Type) -> Type) -> Type -> Type -> Type
Tasks c k v = k -> Maybe (Task c k v)

data Const m a = MkConst m

Functor (Const m) where
  map _ (MkConst m) = MkConst m

[const] Monoid m => Applicative (Const m) where
  pure _ = MkConst neutral
  (MkConst x) <*> (MkConst y) = MkConst (x <+> y)


sprsh1 : Tasks Applicative String Integer
sprsh1 "B1" = Just $ MkTask $ \constr, fetch => B1 @{constr} fetch
  where
    B1 : Applicative f => (String -> f Integer) -> f Integer
    B1 fetch = (+) <$> fetch "A1" <*> fetch "A2"
sprsh1 "B2" = Just $ MkTask $ \constr, fetch => B2 @{constr} fetch
  where
    B2 : Applicative f => (String -> f Integer) -> f Integer
    B2 fetch = (* 2) <$> fetch "B1"
sprsh1 _ = Nothing

dependencies : Task Applicative k v -> List k
dependencies (MkTask task) = let (MkConst xs) = task const (\k => MkConst [k]) in xs

test1 : Maybe (List String)
test1 = sprsh1 "B1" >>= \task => Just $ dependencies task

test2 : Maybe (List String)
test2 = sprsh1 "B2" >>= \task => Just $ dependencies task
