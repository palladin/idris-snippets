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

record Op (argsN : Nat) (size : Nat) where
  constructor MkOp
  id : Int
  func : Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Expr BoolT
  str : Vect argsN String -> String

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

lookupOp : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Vect opsN (Op argsN size) -> Expr BoolT
lookupOp {size} opPos instrVal args ops = or [ite (opPos == (bv (id op) size)) (func op instrVal args) (bool False) | op <- ops]

checkInstr : Vect n (Instr argsN size) -> Expr BoolT
checkInstr [] = bool True
checkInstr [instr] = and [isVar arg == bool True | arg <- args instr]
checkInstr (instr :: instrs) = and $ [or [instrPos arg == pos instr' | instr' <- instrs] | arg <- args instr] ++ [checkInstr instrs]


evalInstr : Vect opsN (Op argsN size) -> Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Expr BoolT
evalInstr {argsN} ops vars instrs = and [and [assocArg vars instrs instr, lookupOp (op instr) (val instr) (map val $ args instr) ops] | instr <- instrs]
  where
    assocArg : Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Instr argsN size -> Expr BoolT
    assocArg vars instrs instr = and $ tabulate (\i => let arg = index i (args instr) in ite (isVar arg) (lookupVar (varPos arg) (val arg) vars)
                                                                                                         (lookupInstr (instrPos arg) (val arg) instrs))

ops : Vect 3 (Op 2 8)
ops = [MkOp 0 (\r, arg => r == bvand (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " bvand " ++ (index 1 args)),
       MkOp 1 (\r, arg => r == bvor (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " bvor " ++ (index 1 args)),
       MkOp 2 (\r, arg => r == bvnot (index 0 arg)) (\args => "bvnot " ++ (index 0 args))]


solver : Smt ()
solver = do setOption ":pp.bv-literals false"
            vars <- declareVars (varNames {n = 1} "var" ) (BitVecT 8)
            argIsVar <- declareVars (varNames' {n = 2} {m = 1} "argIsVar") BoolT
            argVarPos <- declareVars (varNames' {n = 2} {m = 1} "argVarPos") (BitVecT 8)
            argInstrPos <- declareVars (varNames' {n = 2} {m = 1} "argInstrPos") (BitVecT 8)
            argVal <- declareVars (varNames' {n = 2} {m = 1} "argVal") (BitVecT 8)
            instrVal <- declareVars (varNames {n = 1} "instrVal") (BitVecT 8)
            instrOp <- declareVars (varNames {n = 1} "instrOp") (BitVecT 8)
            let vps = createVarPos (toVect vars)
            let args = createArgs (toVect argIsVar) (toVect argVarPos) (toVect argInstrPos) (toVect argVal)
            let instrs = createInstrs (toVect instrVal) (toVect instrOp) args
            assert $ checkInstr instrs
            assert $ evalInstr ops vps instrs
            assert $ val (index 0 instrs) == bvnot (var  (index 0 vps))
            checkSat
            getModel
            end

run : IO ()
run = do maybe <- sat solver
         putStrLn $ show maybe
         pure ()
