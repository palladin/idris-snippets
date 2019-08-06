module Expr

%access public export


data TypeT : Type where
  UnitT : TypeT
  IntT : TypeT
  DoubleT : TypeT
  BoolT : TypeT
  ArrayT : TypeT -> TypeT
  VarT : TypeT -> TypeT
  ArrowT : TypeT -> TypeT -> TypeT

Show TypeT where
  show UnitT = "unit"
  show IntT = "int"
  show DoubleT = "double"
  show BoolT = "bool"
  show (ArrayT typ) = show typ ++ " []"
  show (VarT typ) = show typ ++ " ref"
  show (ArrowT arg res) = "(" ++ show arg ++ " -> " ++ show res ++ ")"


interface Symantics (rep : TypeT -> Type) where
  defaultof : rep a
  int : Int -> rep IntT
  double : Double -> rep DoubleT
  bool : Bool -> rep BoolT
  (==) : rep IntT -> rep IntT -> rep BoolT
  (>) : rep IntT -> rep IntT -> rep BoolT
  (<) : rep IntT -> rep IntT -> rep BoolT
  (&&) : rep BoolT -> rep BoolT -> rep BoolT
  (||) : rep BoolT -> rep BoolT -> rep BoolT
  not : rep BoolT -> rep BoolT
  (+) : rep IntT -> rep IntT -> rep IntT
  (<+>) : rep DoubleT -> rep DoubleT -> rep DoubleT
  (*) : rep IntT -> rep IntT -> rep IntT
  (<*>) : rep DoubleT -> rep DoubleT -> rep DoubleT
  ite : rep BoolT -> rep a -> rep a -> rep a
  it : rep BoolT -> rep UnitT -> rep UnitT
  deref : rep (VarT a) -> rep a
  assign : rep a -> rep (VarT a) -> rep UnitT
  newVar : rep a -> (rep (VarT a) -> rep b) -> rep b
  letVal : rep a -> (rep a -> rep b) -> rep b
  index : rep IntT -> rep (ArrayT a) -> rep a
  length : rep (ArrayT a) -> rep IntT
  while : rep BoolT -> rep UnitT -> rep UnitT
  seq : rep a -> rep b -> rep b
  seqs : List (rep UnitT) -> rep UnitT
  lam : (rep a -> rep b) -> rep (ArrowT a b)
  app : rep (ArrowT a b) -> rep a -> rep b

data Code : TypeT -> Type where
  C : (Int -> String) -> Code a

Symantics Code where
  defaultof {a = UnitT} = C (\_ => "()")
  defaultof {a = IntT} = C (\_ => "0")
  defaultof {a = DoubleT} = C (\_ => "0")
  defaultof {a = BoolT} = C (\_ => "false")
  defaultof {a = (ArrayT x)} = C (\_ => "null")
  defaultof {a = (VarT x)} = C (\_ => "null")
  defaultof {a = (ArrowT x y)} = C (\_ => "null")
  int x = C (\_ => show x)
  double x = C (\_ => show x)
  bool x = C (\_ => if x then "true" else "false")
  (==) (C l) (C r) = C (\v => "( " ++ l v ++ " = " ++ r v ++ " )")
  (>) (C l) (C r) = C (\v => "( " ++ l v ++ " > " ++ r v ++ " )")
  (<) (C l) (C r) = C (\v => "( " ++ l v ++ " < " ++ r v ++ " )")
  (&&) (C l) (C r) = C (\v => "( " ++ l v ++ " && " ++ r v ++ " )")
  (||) (C l) (C r) = C (\v => "( " ++ l v ++ " || " ++ r v ++ " )")
  not (C c) = C (\v => "not (" ++ c v ++ " )")
  (+) (C l) (C r) = C (\v => "( " ++ l v ++ " + " ++ r v ++ " )")
  (<+>) (C l) (C r) = C (\v => "( " ++ l v ++ " + " ++ r v ++ " )")
  (*) (C l) (C r) = C (\v => "( " ++ l v ++ " * " ++ r v ++ " )")
  (<*>) (C l) (C r) = C (\v => "( " ++ l v ++ " * " ++ r v ++ " )")
  ite (C b) (C l) (C r) = C (\v => "(if " ++ b v ++ " then " ++ l v ++ " else " ++ r v ++ ")")
  it (C b) (C t) = C (\v => "(if " ++ b v ++ " then " ++ t v ++ ")")
  deref (C x) = C (\v => "!" ++ x v)
  assign (C val) (C var) = C (\v => var v ++ " := " ++ val v)
  newVar {a} (C s) f = C (\v => let x = "x" ++ show v in
                                let (C c) = f $ the (Code (VarT a)) (C (\_ => x)) in
                                "let " ++ x ++ " = ref " ++ s v ++ " in " ++ c (v + 1))
  letVal (C s) f = C (\v => let x = "x" ++ show v in
                            let (C c) = f $ C (\_ => x) in
                            "let " ++ x ++ " = " ++ s v ++ " in " ++ c (v + 1))
  index (C i) (C arr) = C (\v => arr v ++ ".[" ++ i v ++ "]")
  length (C arr) = C (\v => arr v ++ ".Length")
  while (C p) (C b) = C (\v => "(while " ++ p v ++ " do " ++ b v ++ ")")
  seq (C fs) (C sn) = C (\v => "(" ++ fs v ++ "; " ++ sn v ++ ")")
  seqs steps = foldr seq defaultof steps
  lam {a} f = C (\v => let x = "x" ++ show v in
                       let (C g) = f (C (\_ => x)) in
                       "(fun (" ++ x ++ " : " ++ show a ++ ") -> " ++ g (v + 1) ++ ")")
  app (C f) (C g) = C (\v => "(" ++ f v ++ " " ++ g v ++ ")")


compile : Code a -> String
compile code = let (C c) = code in c 0
