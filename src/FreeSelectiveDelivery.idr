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

runSelect : Selective g => ({x : Type} -> f x -> g x) -> Select f a -> g a
runSelect nat (Pure x) = pure x
runSelect nat (SelectC fe ff) = select (runSelect nat fe) (nat ff)

whenS : Selective f => f Bool -> f () -> f ()
whenS fb fu = select (selector fb) (effect fu)
  where
    selector : f Bool -> f (Either () ())
    selector fb = map (\x => if x then Left () else Right ()) fb
    effect : f () -> f (() -> ())
    effect fu = map const fu

Selective IO where
  select fb ff = fb >>= \e => case e of Left a => map (\f => f a) ff
                                        Right b => pure b

data Teletype : Type -> Type where
  GetLine : Teletype String
  PutStrLn : String -> Teletype ()

interface Serialize (f : Type -> Type) where
  serialize : f a -> (String, String)
interface Deserialize (f : Type -> Type) where
  deserialize : f a -> (String, String) -> Maybe (f a)

Serialize Teletype where
  serialize GetLine = ("GetLine", "")
  serialize (PutStrLn x) = ("PutStrLn", x)

Deserialize Teletype where
  deserialize GetLine ("GetLine", "") = Just $ GetLine
  deserialize (PutStrLn _) ("PutStrLn", s) = Just $ PutStrLn s
  deserialize _ _ = Nothing

data Action : (Type -> Type) -> Type -> Type where
  ActionC : f r -> (r -> a) -> Action f a

Functor (Action f) where
  map f (ActionC c k) = ActionC c (f . k)

Program : (Type -> Type) -> Type -> Type
Program f a = Select (Action f) a

serializeP : Serialize f => Program f a -> List (String, String)
serializeP (Pure _) = []
serializeP (SelectC fs (ActionC c _)) = serialize c :: serializeP fs

deserializeP : Deserialize f => Program f a -> List (String, String) -> Maybe (Program f a)
deserializeP (Pure x) [] = Just $ Pure x
deserializeP (SelectC ff (ActionC c k)) (s :: ss) with (deserialize c s)
  deserializeP (SelectC ff (ActionC c k)) (s :: ss) | Nothing = Nothing
  deserializeP (SelectC ff (ActionC c k)) (s :: ss) | (Just c') = deserializeP ff ss >>= (\ff' => pure $ SelectC ff' (ActionC c' k))
deserializeP _ _ = Nothing


effect : f r -> Program f r
effect c = SelectC (Pure (Left ())) (ActionC c const)

getLine : Program Teletype String
getLine = effect GetLine

putStrLn : String -> Program Teletype ()
putStrLn s = effect (PutStrLn s)

pingPongS : String -> Program Teletype ()
pingPongS s = whenS (map (== "ping") getLine) (putStrLn s)

toIO : Action Teletype a -> IO a
toIO (ActionC GetLine k) = getLine >>= (\x => pure $ k x)
toIO (ActionC (PutStrLn s) k) = putStrLn s >>= (\x => pure $ k x)

testIO : IO ()
testIO = runSelect toIO (pingPongS "pong")

testSerialize : List (String, String)
testSerialize = serializeP (pingPongS "ppong")

testDeserialize : IO ()
testDeserialize = case deserializeP (pingPongS "pong") testSerialize of
                      Nothing => pure ()
                      Just p => runSelect toIO p
