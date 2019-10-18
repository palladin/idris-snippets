module SMTLib

import Data.Vect

%access public export

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
  VarExpr : String -> (t : TypeT) -> Expr t
  BoolExpr : Bool -> Expr BoolT
  BvExpr : Int -> (n : Nat) -> Expr (BitVecT n)
  BvAddExpr : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  BvMulExpr : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  BvAndExpr : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  BvOrExpr : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
  BvNotExpr : Expr (BitVecT n) -> Expr (BitVecT n)
  IntExpr : Int -> Expr (NumT IntT)
  RealExpr : Double -> Expr (NumT RealT)
  AddExpr : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
  MulExpr : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
  EqualExpr : Expr a -> Expr a -> Expr BoolT
  DistinctExpr : Vect n (Expr a) -> Expr BoolT
  LessOrEqualExpr : Expr (NumT a) -> Expr (NumT a) -> Expr BoolT
  AndExpr : Vect n (Expr BoolT) -> Expr BoolT
  OrExpr : Vect n (Expr BoolT) -> Expr BoolT
  NotExpr : Expr BoolT -> Expr BoolT
  IteExpr : Expr BoolT -> Expr a -> Expr a -> Expr a



bool : Bool -> Expr BoolT
bool x = BoolExpr x

bv : Int -> (n : Nat) -> Expr (BitVecT n)
bv x n = BvExpr x n

int : Int -> Expr (NumT IntT)
int x = IntExpr x

real : Double -> Expr (NumT RealT)
real x = RealExpr x

bvadd : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
bvadd l r = BvAddExpr l r

bvmul : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
bvmul l r = BvMulExpr l r

bvand : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
bvand l r = BvAndExpr l r

bvor : Expr (BitVecT n) -> Expr (BitVecT n) -> Expr (BitVecT n)
bvor l r = BvOrExpr l r

bvnot : Expr (BitVecT n) -> Expr (BitVecT n)
bvnot x = BvNotExpr x

(+) : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
(+) l r = AddExpr l r

(*) : Expr (NumT a) -> Expr (NumT a) -> Expr (NumT a)
(*) l r = MulExpr l r

(==) : Expr a -> Expr a -> Expr BoolT
(==) l r = EqualExpr l r

distinct : Vect n (Expr a) -> Expr BoolT
distinct xs = DistinctExpr xs

(<=) : Expr (NumT a) -> Expr (NumT a) -> Expr BoolT
(<=) l r = LessOrEqualExpr l r

(&&) : Expr BoolT -> Expr BoolT -> Expr BoolT
(&&) l r = AndExpr [l, r]

(||) : Expr BoolT -> Expr BoolT -> Expr BoolT
(||) l r = OrExpr [l, r]

and : Vect n (Expr BoolT) -> Expr BoolT
and xs = AndExpr xs

or : Vect n (Expr BoolT) -> Expr BoolT
or xs = OrExpr xs

not : Expr BoolT -> Expr BoolT
not x = NotExpr x

ite : Expr BoolT -> Expr a -> Expr a -> Expr a
ite p l r = IteExpr p l r

data Cmd : Type -> Type where
  DeclareVarCmd : String -> (t : TypeT) -> Cmd (Expr t)
  DeclareVarsCmd : Traversable f => f String -> (t : TypeT) -> Cmd (f (Expr t))
  AssertCmd : Expr BoolT -> Cmd ()
  CheckSatCmd : Cmd ()
  GetModelCmd : Cmd ()

declareVar : String -> (t : TypeT) -> Cmd (Expr t)
declareVar v t = DeclareVarCmd v t

declareVars : Traversable f => f String -> (t : TypeT) -> Cmd (f (Expr t))
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

compileExpr : Expr t -> String
compileExpr (VarExpr x t) = x
compileExpr (BoolExpr x) = if x then "true" else "false"
compileExpr (BvExpr x n) = "(_ bv" ++ show x ++ " " ++ show n ++ ")"
compileExpr (IntExpr x) = show x
compileExpr (RealExpr x) = show x
compileExpr (BvAddExpr l r) = "(bvadd " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (BvMulExpr l r) = "(bvmul " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (BvAndExpr l r) = "(bvand " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (BvOrExpr l r) = "(bvor " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (BvNotExpr x) = "(bnot " ++ compileExpr x ++ ")"
compileExpr (AddExpr l r) = "(+ " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (MulExpr l r) = "(* " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (EqualExpr l r) = "(= " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (DistinctExpr xs) = "(distinct " ++ (unlines . toList . map compileExpr) xs ++ ")"
compileExpr (LessOrEqualExpr l r) = "(<= " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"
compileExpr (AndExpr xs) = "(and " ++ (unlines . toList . map compileExpr) xs ++ ")"
compileExpr (OrExpr xs) = "(or " ++ (unlines . toList . map compileExpr) xs ++ ")"
compileExpr (NotExpr x) = "(not " ++ compileExpr x ++ ")"
compileExpr (IteExpr p l r) = "(if " ++ compileExpr p ++ " " ++ compileExpr l ++ " " ++ compileExpr r ++ ")"

compileCmd : Cmd a -> (a, String)
compileCmd (DeclareVarCmd x t) = (VarExpr x t, "(declare-const " ++ x ++ " " ++ show t ++ ")")
compileCmd (DeclareVarsCmd xs t) = (map (\x => VarExpr x t) xs,
                                    (unlines . toList . map (\x => "(declare-const " ++ x ++ " " ++ show t ++ ")")) xs)
compileCmd (AssertCmd e) = ((), "(assert " ++ compileExpr e ++ ")")
compileCmd CheckSatCmd = ((), "(check-sat)")
compileCmd GetModelCmd = ((), "(get-model)")

compile : Smt () -> String
compile (Pure ()) = ""
compile (Bind cmd f) = let (a, s) = compileCmd cmd in
                       let s' = compile $ f a in
                       unlines [s, s']

example0 : Expr BoolT
example0 = (bool True) && (bool True)

example1 : Expr BoolT
example1 = (bv 1 8) == (bv 1 8)

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
example4 = do [x, y] <- declareVars {f = Vect 2} ["x", "y"] BoolT
              assert $ not (x && y) == (not x || not y)
              checkSat
              getModel
              end

print : Smt () -> IO ()
print smt = putStrLn $ compile smt
