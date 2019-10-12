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
  assert : Expr BoolT -> Cmd ()
  checkSat : Cmd ()
  getModel : Cmd ()
  (>>=) : Cmd a -> (a -> Cmd b) -> Cmd b

  bool : Bool -> Expr BoolT
  bv : Int -> (n : Nat) -> Expr (BitVecT n)
  int : Int -> Expr IntT
  real : Double -> Expr RealT
  bvadd : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bvmul : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  (+) : Expr IntT -> Expr IntT -> Expr IntT
  (*) : Expr IntT -> Expr IntT -> Expr IntT
  (==) : Expr a -> Expr a -> Expr BoolT
  (&&) : Expr BoolT -> Expr BoolT -> Expr BoolT
  (||) : Expr BoolT -> Expr BoolT -> Expr BoolT
  not : Expr BoolT -> Expr BoolT
  ite : Expr BoolT -> Expr a -> Expr a -> Expr a

Smt where
  Expr _ = String
  Cmd a = (a, String)

  assert e = ((), "(assert " ++ e ++ ")")
  checkSat = ((), "(check-sat)")

  bool x = if x then "true" else "false"
  bv v n = "(_ bv" ++ show v ++ " " ++ show n ++ ")"
  (==) l r = "(= " ++ l ++ " " ++ r ++ ")"
  not x = "(not " ++ x ++ ")"

example0 : Smt => Expr BoolT
example0 = (bool True) == (bool True)

example1 : Smt => Expr BoolT
example1 = (bv 1 8) == (bv 1 8)

example2 : Smt => Cmd ()
example2 = checkSat
