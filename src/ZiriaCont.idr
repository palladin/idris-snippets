module ZiriaCont


data FreerCont : (f : Type -> Type) -> Type -> Type where
  Cont : ({r : Type} -> (a -> r) -> ({x : Type} -> f x -> (x -> r) -> r) -> r) -> FreerCont f a

return : a -> FreerCont f a
return x = Cont (\k, _ => k x)

(>>=) : FreerCont f a -> (a -> FreerCont f b) -> FreerCont f b
(>>=) (Cont g) f = Cont (\k, imp => g (\x => let (Cont g') = f x in g' k imp) imp)

data Zir : (i : Type) -> (o : Type) -> (v : Type) -> Type where
  Yield : o -> Zir i o ()
  NeedInput : Zir i o i

emit : o -> FreerCont (Zir i o) ()
emit o = Cont (\k, imp => imp (Yield o) k)

take : FreerCont (Zir i o) i
take = Cont (\k, imp => imp NeedInput k)

data Rec : (x : Type) -> (r : Type) -> Type where
  K : ((x -> Rec x r -> r) -> r) -> Rec x r

gImp :  ({y : Type} -> Zir i o y -> (y -> r) -> r) -> Zir m o x -> (x -> Rec m r -> r) -> Rec m r -> r
gImp imp (Yield ot) k rec = imp (Yield ot) (\() => k () rec)
gImp imp NeedInput k (K k') = k' k

fImp :  ({y : Type} -> Zir i o y -> (y -> r) -> r) -> Zir i m x -> (x -> (m -> Rec m r -> r) -> r) -> (m -> Rec m r -> r) -> r
fImp imp (Yield ot) k k' = k' ot (K (k ()))
fImp imp NeedInput k k' = imp NeedInput (\i => k i k')

infixl 9 >>>
(>>>) : FreerCont (Zir i m) v -> FreerCont (Zir m o) v -> FreerCont (Zir i o) v
(>>>) (Cont f) (Cont g) = Cont (\k, imp => let g' = g (\x, _ => k x) (gImp imp) in
                                           let f' = f (\x, _ => k x) (fImp imp) in
                                           g' (K f'))


imp : Zir i o x -> (x -> Stream i -> (v, List o)) -> Stream i -> (v, List o)
imp (Yield x) k xs = let (v, xs') = k () xs in (v, x :: xs')
imp NeedInput k (x :: xs) = k x xs

run : FreerCont (Zir i o) v -> Stream i -> (v, List o)
run (Cont f) = f k imp
 where
   k : v -> Stream i -> (v, List o)
   k x _ = (x, [])


example : FreerCont (Zir Int Int) Int
example = do x <- take
             emit (x + 1)
             y <- take
             emit (y + 2)
             return (x + y)

test : (Int, List Int)
test = run example [1..]

stream1 : FreerCont (Zir Int Int) Int
stream1 = do emit 1
             emit 2
             return 41

stream2 : FreerCont (Zir Int Int) Int
stream2 = do x <- take
             y <- take
             emit (x + y)
             return 42

test' : (Int, List Int)
test' = run (stream1 >>> stream2) [1..]
