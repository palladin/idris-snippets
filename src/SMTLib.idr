module SMTLib

data TypeT : Type where
  BoolT : TypeT
  IntT : TypeT
  RealT : TypeT
  BitVecT : Nat -> TypeT

Show TypeT where
  show BoolT = "Bool"
  show IntT = "Int"
  show RealT = "Real"
  show (BitVecT n) = "BitVec " ++ show n

interface Smt where
  Expr : TypeT -> Type
  Cmd : Type -> Type

  createVar : String -> (t : TypeT) -> Cmd (Expr t)
  (>>=) : Cmd a -> (a -> Cmd b) -> Cmd b

  bool : Bool -> Expr BoolT
  bInt : Int -> (n : Nat) -> Expr (BitVecT n)
  int : Int -> Expr IntT
  real : Double -> Expr RealT
  bAdd : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bMul : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  (==) : Expr a -> Expr a -> Expr BoolT
  (&&) : Expr BoolT -> Expr BoolT -> Expr BoolT
  (||) : Expr BoolT -> Expr BoolT -> Expr BoolT
  not : Expr BoolT -> Expr BoolT
  ite : Expr BoolT -> Expr a -> Expr a -> Expr a

Smt where
  Expr _ = String
  Cmd _ = String

  bool x = if x then "true" else "false"
  (==) l r = "(= " ++ l ++ " " ++ r ++ ")"
  not x = "(not " ++ x ++ ")"

example0 : Smt => Expr BoolT
example0 = (bool True) == (bool False)
