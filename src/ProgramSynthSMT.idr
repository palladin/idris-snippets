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
  val : Expr (BitVecT size)

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

createArgs : Vect n (Vect argsN (Expr BoolT)) -> Vect n (Vect argsN (Expr (BitVecT size))) -> Vect n (Vect argsN (Expr (BitVecT size))) ->  Vect n (Vect argsN (Expr (BitVecT size))) -> Vect n (Vect argsN (Arg size))
createArgs isVars vars instrs vals = tabulate (\i0 => tabulate (\i1 => MkArg (index i0 i1 isVars) (index i0 i1 vars) (index i0 i1 instrs) (index i0 i1 vals)))

createInstrs : Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Vect argsN (Arg size)) -> Vect n (Instr argsN size)
createInstrs {size} vals ops args = tabulate (\i => MkInstr (bv (finToInt i) size) (index i vals) (index i ops) (index i args))

lookupInstr : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (Instr argsN size) -> Expr BoolT
lookupInstr p v instrs = or [ite (p == pos instr) (v == val instr) (bool False) | instr <- instrs]

varNames : String -> Tensor [n] String
varNames name = toTensor $ tabulate (\i => name ++ "_" ++ show (finToNat i))

varNames' : String -> Tensor [n, m] String
varNames' name = toTensor $ tabulate (\i0 => tabulate (\i1 => name ++ "_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

Op : (size : Nat) -> (argsN : Nat) -> Type
Op size argsN = (Int, Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Expr BoolT)

lookupOp : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Vect opsN (Op size argsN) -> Expr BoolT
lookupOp {size} opPos instrVal args ops = or [ite (opPos == (bv i size)) (op instrVal args) (bool False) | (i, op) <- ops]

evalInstr : Vect opsN (Op size argsN) -> Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Expr BoolT
evalInstr {argsN} ops vars instrs = and [and [assocArg vars instrs instr, lookupOp (op instr) (val instr) (map val $ args instr) ops] | instr <- instrs]
  where
    assocArg : Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Instr argsN size -> Expr BoolT
    assocArg vars instrs instr = and $ tabulate (\i => let arg = index i (args instr) in ite (isVar arg) (lookupVar (varPos arg) (val arg) vars)
                                                                                                         (lookupInstr (instrPos arg) (val arg) instrs))

ops : Vect 3 (Op 8 2)
ops = [(0, \r, arg => r == bvand (index 0 arg) (index 1 arg)),
       (1, \r, arg => r == bvor (index 0 arg) (index 1 arg)),
       (2, \r, arg => r == bvnot (index 0 arg))]


solver : Smt ()
solver = do setOption ":pp.bv-literals false"
            vars <- declareVars (varNames {n = 2} "var" ) (BitVecT 8)
            argIsVar <- declareVars (varNames' {n = 2} {m = 2} "argIsVar") BoolT
            argVarPos <- declareVars (varNames' {n = 2} {m = 2} "argVarPos") (BitVecT 8)
            argInstrPos <- declareVars (varNames' {n = 2} {m = 2} "argInstrPos") (BitVecT 8)
            argVal <- declareVars (varNames' {n = 2} {m = 2} "argVal") (BitVecT 8)
            instrVal <- declareVars (varNames {n = 2} "instrVal") (BitVecT 8)
            instrOp <- declareVars (varNames {n = 2} "instrOp") (BitVecT 8)
            let vps = createVarPos (toVect vars)
            let args = createArgs (toVect argIsVar) (toVect argVarPos) (toVect argInstrPos) (toVect argVal)
            let instrs = createInstrs (toVect instrVal) (toVect instrOp) args
            x <- declareVar "x" (BitVecT 8)
            assert $ x == (bv 42 8)
            assert $ lookupInstr (bv 1 8) x instrs
            checkSat
            getModel
            end

run : IO ()
run = do maybe <- sat solver
         putStrLn $ show maybe
         pure ()
