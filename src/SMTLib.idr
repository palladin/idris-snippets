module SMTLib

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


data Expr : TypeT -> Type where
  EqualExpr : Expr a -> Expr a -> Expr BoolT
  BoolExpr : Bool -> Expr BoolT
  AndExpr : Expr BoolT -> Expr BoolT -> Expr BoolT

(==) : Expr a -> Expr a -> Expr BoolT
(==) l r = EqualExpr l r
bool : Bool -> Expr BoolT
bool x = BoolExpr x
(&&) : Expr BoolT -> Expr BoolT -> Expr BoolT
(&&) l r = AndExpr l r

data Cmd : Type -> Type where
  DeclareVarCmd : String -> (t : TypeT) -> Cmd (Expr t)
  DeclareVarsCmd : Vect n String -> (t : TypeT) -> Cmd (Vect n (Expr t))
  AssertCmd : Expr BoolT -> Cmd ()
  CheckSatCmd : Cmd ()
  GetModelCmd : Cmd ()

declareVar : String -> (t : TypeT) -> Cmd (Expr t)
declareVar v t = DeclareVarCmd v t

declareVars : Vect n String -> (t : TypeT) -> Cmd (Vect n (Expr t))
declareVars vs t = DeclareVarsCmd vs t

assert : Expr BoolT -> Cmd ()
assert e = AssertCmd e

checkSat : Cmd ()
checkSat = CheckSatCmd

getModel : Cmd ()
getModel = GetModelCmd

data Smt : Type -> Type where
  Pure : a -> Smt a
  Bind : Cmd a -> (a -> Smt b) -> Smt b

pure : a -> Smt a
pure x = Pure x

(>>=) : Cmd a -> (a -> Smt b) -> Smt b
(>>=) cmd f = Bind cmd f

end : Smt ()
end = Pure ()

compileCmd : Cmd a -> (a, String)

compile : Smt () -> String
compile (Pure ()) = ""
compile (Bind cmd f) = let (a, s) = compileCmd cmd in
                       let s' = compile $ f a in
                       s ++ "\n" ++ s'

example0 : Expr BoolT
example0 = (bool True) && (bool True)



--example1 : Expr BoolT
--example1 = (bv 1 8) == (bv 1 8)

example2 : Cmd ()
example2 = checkSat

example3 : Smt ()
example3 = do x <- declareVar "x" BoolT
              y <- declareVar "y" BoolT
              assert $ x && y
              checkSat
              getModel
              end

example4 : Smt ()
example4 = do [x, y] <- declareVars ["x", "y"] BoolT
              assert $ x && y
              checkSat
              getModel
              end
