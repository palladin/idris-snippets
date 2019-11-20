module ProgramSynthSMT


import Data.Vect
import src.SMTLib
import src.Tensor


record VarPos (size : Nat) where
  constructor MkVar
  pos : Expr (BitVecT size)
  var : Expr (BitVecT size)

record Arg (size : Nat) where
  constructor MkArg
  isVar : Expr BoolT
  varPos : Expr (BitVecT size)
  instrPos : Expr (BitVecT size)

record Instr (argsN : Nat) (size : Nat) where
  constructor MkInstr
  pos : Expr (BitVecT size)
  val : Expr (BitVecT size)
  op : Expr (BitVecT size)
  args : Vect argsN (Arg size)

createVarPos : Vect n (Expr (BitVecT size)) -> Vect n (VarPos size)
createVarPos {n} {size} vs = tabulate (\i => MkVar (bv (finToInt i) size) (index i vs))

lookupVar : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (VarPos size) -> Expr BoolT
lookupVar p v vs = or [ite (p == pos vp) (v == var vp) (bool False) | vp <- vs]

createArgs : Vect n (Expr BoolT) -> Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Arg size)
createArgs isVars vars instrs = tabulate (\i => MkArg (index i isVars) (index i vars) (index i instrs))

createInstrs : Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Vect argsN (Arg size)) -> Vect n (Instr argsN size)
createInstrs {size} vals ops args = tabulate (\i => MkInstr (bv (finToInt i) size) (index i vals) (index i ops) (index i args))

lookupInstr : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (Instr argsN size) -> Expr BoolT
lookupInstr p v instrs = or [ite (p == pos instr) (v == val instr) (bool False) | instr <- instrs]

varNames : String -> Tensor [n] String
varNames name = toTensor $ tabulate (\i => name ++ "_" ++ show (finToNat i))

varNames' : String -> Tensor [n, m] String
varNames' name = toTensor $ tabulate (\i0 => tabulate (\i1 => name ++ "_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

solver : Smt ()
solver = do setOption ":pp.bv-literals false"
            vars <- declareVars (varNames "var" {n = 2}) (BitVecT 8)
            let vars = toVect vars
            let vps = createVarPos vars
            assert $ var (index 0 vps) == (bv 42 8)
            var <- declareVar "x" (BitVecT 8)
            assert $ lookupVar (bv 0 8) var vps
            checkSat
            getModel
            end

run : IO ()
run = do maybe <- sat solver
         putStrLn $ show maybe
         pure ()
