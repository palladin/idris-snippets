module FreeDelivery

-- Based on https://www.cs.ox.ac.uk/jeremy.gibbons/publications/delivery.pdf

data FreeA : (Type -> Type) -> Type -> Type where
  Pure : a -> FreeA f a
  More : f (a -> b) -> FreeA f a -> FreeA f b

Functor f => Functor (FreeA f) where
  map f (Pure x) = Pure $ f x
  map f (More fab ffa) = More (map (f .) fab) ffa

Functor f => Applicative (FreeA f) where
 pure x = Pure x

 (Pure f) <*> fa = map f fa
 (More h fa') <*> fa = More (map uncurry h) (pure (\x, y => (x, y)) <*> fa' <*> fa)

data Command : Type -> Type where
  Say : String -> Command ()
  Toast : Int -> Command ()
  Sense : Command Int

interface SerializeCommand a where
  serialize : a -> (String, String)
interface DeserializeCommand a where
    deserialize : a -> (String, String) -> Maybe a

SerializeCommand (Command a) where
  serialize (Say x) = ("Say", x)
  serialize (Toast x) = ("Toast", show x)
  serialize Sense = ("Sense", "")

DeserializeCommand (Command a) where
  deserialize (Say _) ("Say", s) = Just $ Say s
  deserialize (Toast _) ("Toast", s) = Just $ Toast (cast s)
  deserialize Sense ("Sense", s) = Just $ Sense
  deserialize _ _ = Nothing

data ActionA : Type -> Type where
  Con : Command r -> (r -> a) -> ActionA a

Functor ActionA where
  map f (Con c k) = Con c (f . k)

ProgramA : Type -> Type
ProgramA a = FreeA ActionA a

effectA : Command r -> ProgramA r
effectA c = More (Con c (\r, () => r)) (Pure ())

sayA : String -> ProgramA ()
sayA s = effectA (Say s)

toastA : Int -> ProgramA ()
toastA n = effectA (Toast n)

senseA : ProgramA Int
senseA = effectA Sense

straightA : Int -> ProgramA (Int, Int)
straightA n = pure (\t, (), t' => (t, t')) <*> senseA <*> toastA n <*> senseA

serializeA : ProgramA a -> List (String, String)
serializeA (Pure _) = []
serializeA (More (Con c _) fa') = serialize c :: serializeA fa'

deserializeA : ProgramA a -> List (String, String) -> Maybe (ProgramA a)
deserializeA (Pure x) [] = Just $ Pure x
deserializeA (More (Con c k) fa') (s :: ss) with (deserialize c s)
  deserializeA (More (Con c k) fa') (s :: ss) | Nothing = Nothing
  deserializeA (More (Con c k) fa') (s :: ss) | (Just c') = pure (More (Con c' k)) <*> deserializeA fa' ss
deserializeA _ _ = Nothing

testSerialize : List (String, String)
testSerialize = serializeA (straightA 1)

testDeserialize : Maybe (ProgramA (Int, Int))
testDeserialize = deserializeA (straightA 2) testSerialize
