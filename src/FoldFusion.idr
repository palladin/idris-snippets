module FoldFusion

Array : Type -> Type
Var : Type -> Type -> Type

interface Symantics (rep : Type -> Type) where
  int : Int -> rep Int
  bool : Bool -> rep Bool
  (==) : rep Int -> rep Int -> rep Bool
  (>) : rep Int -> rep Int -> rep Bool
  (<) : rep Int -> rep Int -> rep Bool
  (&&) : rep Bool -> rep Bool -> rep Bool
  (||) : rep Bool -> rep Bool -> rep Bool
  (+) : rep Int -> rep Int -> rep Int
  (*) : rep Int -> rep Int -> rep Int
  ite : rep Bool -> rep a -> rep a -> rep a
  deref : rep (Var s a) -> rep a
  assign : rep a -> rep (Var s a) -> rep ()
  newVar : rep a -> ({s : Type} -> rep (Var s a) -> rep b) -> rep b
  foreach : rep (Array a) -> (rep a -> rep ()) -> rep ()
  seq : rep a -> rep b -> rep b
  lam : (rep a -> rep b) -> rep (a -> b)
  app : rep (a -> b) -> rep a -> rep b

data Code : Type -> Type where
  C : (Int -> String) -> Code a


Symantics Code where
  int x = C (\_ => show x)
  bool x = C (\_ => if x then "true" else "false")
  (==) (C l) (C r) = C (\v => "( " ++ l v ++ " = " ++ r v ++ " )")
  (>) (C l) (C r) = C (\v => "( " ++ l v ++ " > " ++ r v ++ " )")
  (<) (C l) (C r) = C (\v => "( " ++ l v ++ " < " ++ r v ++ " )")
  (&&) (C l) (C r) = C (\v => "( " ++ l v ++ " && " ++ r v ++ " )")
  (||) (C l) (C r) = C (\v => "( " ++ l v ++ " || " ++ r v ++ " )")
  (+) (C l) (C r) = C (\v => "( " ++ l v ++ " + " ++ r v ++ " )")
  (*) (C l) (C r) = C (\v => "( " ++ l v ++ " * " ++ r v ++ " )")
  ite (C b) (C l) (C r) = C (\v => "(if " ++ b v ++ " then " ++ l v ++ " else " ++ r v ++ ")")
  deref (C x) = C (\v => "!" ++ x v)
  assign (C val) (C var) = C (\v => var v ++ " := " ++ val v)
  newVar {a} (C s) f = C (\v => let x = "x" ++ show v in
                                let (C c) = f $ the (Code (Var () a)) (C (\_ => x)) in
                                "let " ++ x ++ " = ref " ++ s v ++ " in " ++ c (v + 1))
  foreach (C arr) f = C (\v =>  let x = "x" ++ show v in
                                let (C c) = f (C (\_ => x)) in
                                "(for " ++ x ++ " in " ++ arr v ++ " do " ++ c (v + 1) ++ ")")
  seq (C fs) (C sn) = C (\v => "(" ++ fs v ++ "; " ++ sn v ++ ")")
  lam f = C (\v => let x = "x" ++ show v in
                   let (C g) = f (C (\_ => x)) in
                   "(fun " ++ x ++ " -> " ++ g (v + 1) ++ ")" )
  app (C f) (C g) = C (\v => "(" ++ f v ++ " " ++ g v ++ ")" )


data Fold : (rep : Type -> Type) -> (a : Type) -> Type where
  FC : ({r : Type} -> (rep a -> rep r -> rep r) -> rep r -> rep r) -> Fold rep a


ofArray : Symantics rep => rep (Array a) -> Fold rep a
ofArray arr = FC (\f, seed => newVar seed (\v => seq (foreach arr (\x => assign (f x (deref v)) v)) (deref v)))

fold : (rep a -> rep r -> rep r) -> rep r -> Fold rep a -> rep r
fold f seed (FC g) = g f seed

map : (rep a -> rep b) -> Fold rep a -> Fold rep b
map f (FC g) = FC (\h => g (\x, r => h (f x) r))

flatMap : (rep a -> Fold rep b) -> Fold rep a -> Fold rep b
flatMap f (FC g) = FC (\h => g (\x, r => fold h r (f x)))

filter : Symantics rep => (rep a -> rep Bool) -> Fold rep a -> Fold rep a
filter f (FC g) = FC (\h => g (\x, r =>  ite (f x) (h x r) r))

count : Symantics rep => Fold rep a -> rep Int
count = fold (\x, acc => acc + (int 1)) (int 0)

sum : Symantics rep => Fold rep Int -> rep Int
sum = fold (\x, acc => x + acc) (int 0)

example : Symantics rep => rep (Array Int) -> rep Int
example = sum . map (\x => x * (int 2)) . filter (\x => x < (int 5)) . ofArray

test : Code (Array Int -> Int)
test = lam example

code : String
code = let (C c) = test in c 0
