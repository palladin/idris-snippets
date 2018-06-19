module Ziria

-- Based on https://github.com/dimitriv/ziria-sem/blob/master/Haskell/ZirStepper.hs

data ZirS : (s : Type) -> (i : Type) -> (o : Type) -> (v : Type) -> Type where
  Yield : s -> o -> ZirS s i o v
  Skip : s -> ZirS s i o v
  Done : v -> ZirS s i o v
  NeedInput : (i -> s) -> ZirS s i o v

data Zir : (i : Type) -> (o : Type) -> (v : Type) -> Type where
  ZirC : s -> (s -> ZirS s i o v) -> Zir i o v


return : v -> Zir i o v
return v = ZirC () (\() => Done v)

cast : (s -> s') -> ZirS s i o v -> ZirS s' i o v
cast f (Yield s o) = Yield (f s) o
cast f (Skip s) = Skip (f s)
cast f (Done x) = Done x
cast f (NeedInput g) = NeedInput (f . g)

(>>=) : Zir i o v -> (v -> Zir i o w) -> Zir i o w
(>>=) (ZirC x step1) f = ZirC (Left x) (step step1)
  where
    s2step : Zir i o w -> ZirS (Either s (Zir i o w)) i o w
    s2step (ZirC s2 step2) = cast (\x => Right (ZirC x step2)) (step2 s2)
    step : (s -> ZirS s i o v) -> Either s (Zir i o w) -> ZirS (Either s (Zir i o w)) i o w
    step step1 (Right zir) = s2step zir
    step step1 (Left l) with (step1 l)
      step step1 (Left l) | (Yield s1' z) = Yield (Left s1') z
      step step1 (Left l) | (Skip s1') = Skip (Left s1')
      step step1 (Left l) | (Done y) = s2step (f y)
      step step1 (Left l) | (NeedInput g) = NeedInput (\i => Left (g i))



step' : (s1 -> ZirS s1 i m v) -> (s2 -> ZirS s2 m o v) -> (s1, s2) -> ZirS (s1, s2) i o v
step' step1 step2 (s1, s2) with (step2 s2)
  step' step1 step2 (s1, s2) | (Yield s2' ot) = Yield (s1, s2') ot
  step' step1 step2 (s1, s2) | (Skip s2') = Skip (s1, s2')
  step' step1 step2 (s1, s2) | (Done x) = Done x
  step' step1 step2 (s1, s2) | (NeedInput f) with (step1 s1)
    step' step1 step2 (s1, s2) | (NeedInput f) | (Yield s1' ot) = Skip (s1', f ot)
    step' step1 step2 (s1, s2) | (NeedInput f) | (Skip s1') = Skip (s1', s2)
    step' step1 step2 (s1, s2) | (NeedInput f) | (Done x) = Done x
    step' step1 step2 (s1, s2) | (NeedInput f) | (NeedInput g) = NeedInput (\i => ((g i), s2))

infixl 9 >>>
(>>>) : Zir i m v -> Zir m o v -> Zir i o v
(>>>) (ZirC s1 step1) (ZirC s2 step2) = ZirC (s1, s2) (step' step1 step2)

emit : o -> Zir i o ()
emit x = ZirC True aux
  where
    aux : Bool -> ZirS Bool i o ()
    aux False = Done ()
    aux True = Yield False x

take : Zir i o i
take = ZirC Nothing aux
  where
    aux : Maybe i -> ZirS (Maybe i) i o i
    aux Nothing = NeedInput Just
    aux (Just x) = Done x


run : Zir i o v -> Stream i -> (v, List o)
run (ZirC st step) input = loop step [] input (step st)
  where
    loop : (s -> ZirS s i o v) -> List o -> Stream i -> ZirS s i o v -> (v, List o)
    loop step acc input (Yield st ot) = loop step (ot :: acc) input (step st)
    loop step acc input (Skip st) = loop step acc input (step st)
    loop step acc input (Done v) = (v, reverse acc)
    loop step acc (x :: xs) (NeedInput f) = loop step acc xs (step (f x))


example : Zir Int Int Int
example = do x <- take
             emit (x + 1)
             y <- take
             emit (y + 2)
             return (x + y)

test : (Int, List Int)
test = run example [1..]
