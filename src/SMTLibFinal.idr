module SMTLibFinal

import Data.Vect

data NumTyp = IntT | RealT

data TypeT : Type where
  BoolT : TypeT
  NumT : NumTyp -> TypeT
  BitVecT : Nat -> TypeT

Show TypeT where
  show BoolT = "Bool"
  show (NumT IntT) = "Int"
  show (NumT RealT) = "Real"
  show (BitVecT n) = "BitVec " ++ show n

interface Smt where
  Expr : TypeT -> Type
  Cmd : Type -> Type

  (>>=) : Cmd a -> (a -> Cmd b) -> Cmd b
  pure : a -> Cmd a
  declareVar : String -> (t : TypeT) -> Cmd (Expr t)
  declareVars : Vect n String -> (t : TypeT) -> Cmd (Vect n (Expr t))
  assert : Expr BoolT -> Cmd ()
  checkSat : Cmd ()
  getModel : Cmd ()

  bool : Bool -> Expr BoolT
  bv : Int -> (n : Nat) -> Expr (BitVecT n)
  int : Int -> Expr (NumT IntT)
  real : Double -> Expr (NumT RealT)
  bvadd : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bvmul : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bvand : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bvor : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  bvnot : Expr (BitVecT n) -> Expr (BitVecT n)
  (+) : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
  (*) : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
  (==) : Expr a -> Expr a -> Expr BoolT
  (&&) : Expr BoolT -> Expr BoolT -> Expr BoolT
  (||) : Expr BoolT -> Expr BoolT -> Expr BoolT
  not : Expr BoolT -> Expr BoolT
  ite : Expr BoolT -> Expr a -> Expr a -> Expr a

[smt] Smt where
  Expr _ = String
  Cmd a = (a, String)

  (>>=) (a, s) f = let (b, s') = f a in (b, s ++ "\n" ++ s')
  pure x = (x, "")
  declareVar x t = (x, "(declare-const " ++ x ++ " " ++ show t ++ ")")
  declareVars [] t = pure []
  declareVars (x :: xs) t = do x' <- declareVar x t
                               xs' <- declareVars xs t
                               pure $ x' :: xs'
  assert e = ((), "(assert " ++ e ++ ")")
  checkSat = ((), "(check-sat)")
  getModel = ((), "(get-model)")

  bool x = if x then "true" else "false"
  bv v n = "(_ bv" ++ show v ++ " " ++ show n ++ ")"
  int x = show x
  real x = show x
  bvadd l r = "(bvadd " ++ l ++ " " ++ r ++ ")"
  bvmul l r = "(bvmul " ++ l ++ " " ++ r ++ ")"
  bvand l r = "(bvand " ++ l ++ " " ++ r ++ ")"
  bvor l r = "(bvor " ++ l ++ " " ++ r ++ ")"
  bvnot x = "(bvnot " ++ x ++ ")"
  (+) l r = "(+ " ++ l ++ " " ++ r ++ ")"
  (*) l r = "(* " ++ l ++ " " ++ r ++ ")"
  (==) l r = "(= " ++ l ++ " " ++ r ++ ")"
  (&&) l r = "(and " ++ l ++ " " ++ r ++ ")"
  (||) l r = "(or " ++ l ++ " " ++ r ++ ")"
  not x = "(not " ++ x ++ ")"
  ite p l r = "(if " ++ l ++ " " ++ r ++ ")"

example0 : Smt => Expr BoolT
example0 = (bool True) == (bool True)

example1 : Smt => Expr BoolT
example1 = (bv 1 8) == (bv 1 8)

example2 : Smt => Cmd ()
example2 = checkSat

example3 : Smt => Cmd ()
example3 = do x <- declareVar "x" BoolT
              y <- declareVar "y" BoolT
              assert $ not (x && y) == (not y || not y)
              checkSat
              getModel
