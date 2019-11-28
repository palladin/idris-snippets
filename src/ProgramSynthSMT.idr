module ProgramSynthSMT


import Data.Vect
import Data.String
import src.SMTLib
import src.Tensor


record VarPos (size : Nat) where
  constructor MkVar
  pos : Expr (BitVecT size)
  val : Expr (BitVecT size)

record Arg (size : Nat) where
  constructor MkArg
  isVar : Expr BoolT
  varPos : Expr (BitVecT size)
  instrPos : Expr (BitVecT size)
  val : Expr (BitVecT size)

record ArgName (size : Nat) where
  constructor MkArgName
  isVar : String
  varPos : String
  instrPos : String

record Instr (argsN : Nat) (size : Nat) where
  constructor MkInstr
  pos : Expr (BitVecT size)
  val : Expr (BitVecT size)
  op : Expr (BitVecT size)
  args : Vect argsN (Arg size)

record InstrName (argsN : Nat) (size : Nat) where
    constructor MkInstrName
    op : String
    args : Vect argsN (ArgName size)

record Op (argsN : Nat) (size : Nat) where
  constructor MkOp
  id : Int
  func : Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Expr BoolT
  str : Vect argsN String -> String

createVarPos : Vect n (Expr (BitVecT size)) -> Vect n (VarPos size)
createVarPos {n} {size} vs = tabulate (\i => MkVar (bv (finToInt i) size) (index i vs))

lookupVar : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (VarPos size) -> Expr BoolT
lookupVar p v vs = or [ite' (p == pos vp) (v == val vp) (bool False) | vp <- vs]

createArgs : Vect n (Vect argsN (Expr BoolT)) -> Vect n (Vect argsN (Expr (BitVecT size))) -> Vect n (Vect argsN (Expr (BitVecT size))) ->  Vect n (Vect argsN (Expr (BitVecT size))) -> Vect n (Vect argsN (Arg size))
createArgs isVars vars instrs vals = tabulate (\i0 => tabulate (\i1 => MkArg (index i0 i1 isVars) (index i0 i1 vars) (index i0 i1 instrs) (index i0 i1 vals)))

createInstrs : Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Vect argsN (Arg size)) -> Vect n (Instr argsN size)
createInstrs {size} vals ops args = tabulate (\i => MkInstr (bv (finToInt i) size) (index i vals) (index i ops) (index i args))

lookupInstr : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (Instr argsN size) -> Expr BoolT
lookupInstr p v instrs = or [ite' (p == pos instr) (v == val instr) (bool False) | instr <- instrs]

varNames : String -> Tensor [n] String
varNames name = toTensor $ tabulate (\i => name ++ "_" ++ show (finToNat i))

varNames' : String -> Tensor [n, m] String
varNames' name = toTensor $ tabulate (\i0 => tabulate (\i1 => name ++ "_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

lookupOp : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect argsN (Expr (BitVecT size)) -> Vect opsN (Op argsN size) -> Expr BoolT
lookupOp {size} opPos instrVal args ops = or [ite' (opPos == (bv (id op) size)) (func op instrVal args) (bool False) | op <- ops]

checkInstr : Vect n (Instr argsN size) -> Expr BoolT
checkInstr [] = bool True
checkInstr [instr] = and [isVar arg == bool True | arg <- args instr]
checkInstr (instr :: instrs) = and $ [or [instrPos arg == pos instr' | instr' <- instrs] | arg <- args instr] ++ [checkInstr instrs]

evalInstr : Vect opsN (Op argsN size) -> Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Expr BoolT
evalInstr {argsN} ops vars instrs = and [and [assocArg vars instrs instr, lookupOp (op instr) (val instr) (map val $ args instr) ops] | instr <- instrs]
  where
    assocArg : Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Instr argsN size -> Expr BoolT
    assocArg vars instrs instr = and $ tabulate (\i => let arg = index i (args instr) in ite' (isVar arg) (lookupVar (varPos arg) (val arg) vars)
                                                                                                         (lookupInstr (instrPos arg) (val arg) instrs))

InstrsN : Nat
InstrsN = 1

ArgsN : Nat
ArgsN = 2

OpsN : Nat
OpsN = 3

BitSize : Nat
BitSize = 8

ops : Vect OpsN (Op ArgsN BitSize)
ops = [MkOp 0 (\r, arg => r == bvand (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " bvand " ++ (index 1 args)),
       MkOp 1 (\r, arg => r == bvor (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " bvor " ++ (index 1 args)),
       MkOp 2 (\r, arg => r == bvnot (index 0 arg)) (\args => "bvnot " ++ (index 0 args))]

varPosVal : Int -> Tensor [InstrsN] String
varPosVal n = varNames $ "varPosVal" ++ show n

argIsVar : Tensor [ArgsN, InstrsN] String
argIsVar = varNames' "argIsVar"

argVarPos : Tensor [ArgsN, InstrsN] String
argVarPos = varNames' "argVarPos"

argInstrPos : Tensor [ArgsN, InstrsN] String
argInstrPos = varNames' "argInstrPos"

argVal : Int -> Tensor [ArgsN, InstrsN] String
argVal n = varNames' $ "argVal" ++ show n

instrVal : Int -> Tensor [InstrsN] String
instrVal n = varNames $ "instrVal" ++ show n

instrOp : Tensor [InstrsN] String
instrOp = varNames "instrOp"

instrNames : Vect InstrsN (InstrName ArgsN BitSize)
instrNames = tabulate (\i => MkInstrName (index i (toVect instrOp))
                                         (tabulate (\j => MkArgName (index i j (toVect argIsVar))
                                                                    (index i j (toVect argVarPos))
                                                                    (index i j (toVect argInstrPos)))))

solver : List Int -> List Int -> Smt ()
solver input output =
         do setLogic "QF_BV"
            setOption ":pp.bv-literals false"
            let n = 0

            argIsVar <- declareVars argIsVar BoolT
            argVarPos <- declareVars argVarPos (BitVecT BitSize)
            argInstrPos <- declareVars argInstrPos (BitVecT BitSize)
            instrOp <- declareVars instrOp (BitVecT BitSize)
            vars <- declareVars (varPosVal n) (BitVecT BitSize)
            argVal <- declareVars (argVal n) (BitVecT BitSize)
            instrVal <- declareVars (instrVal n) (BitVecT BitSize)

            let vps = createVarPos (toVect vars)
            let args = createArgs (toVect argIsVar) (toVect argVarPos) (toVect argInstrPos) (toVect argVal)
            let instrs = createInstrs (toVect instrVal) (toVect instrOp) args

            assert $ checkInstr instrs
            assert $ evalInstr ops vps instrs
            assert $ val (index 0 instrs) == bvnot (val (index 0 vps))
            checkSat
            getModel
            end

parseBool : String -> Maybe Bool
parseBool "true" = Just True
parseBool "false" = Just False
parseBool _ = Nothing

parseArgs : Model -> Vect n (ArgName size) -> Maybe (Vect n String)
parseArgs {n = Z} model args = Just []
parseArgs {n = (S n)} model ((MkArgName isVar varPos instrPos) :: args) =
  do isVarVal <- lookup isVar model
     isVar <- parseBool isVarVal
     varPosVal <- lookup varPos model
     instrPosVal <- lookup instrPos model
     args <- parseArgs model args
     pure $ [if isVar then "var" ++ varPosVal else "instr" ++ instrPosVal] ++ args

parseInstrs : Model -> Vect opsN (Op argsN size) -> Vect n (InstrName argsN size) -> Maybe (List String)
parseInstrs {n = Z} model ops [] = Just []
parseInstrs {n = S n} model ops ((MkInstrName opStr args) :: instrs) =
    do opVal <- lookup opStr model
       opId <- parseInteger {a = Int} opVal
       op <- find (\op => id op == opId) ops
       args <- parseArgs model args
       instrs <- parseInstrs model ops instrs
       pure $ ["instr" ++ show n ++ " = " ++ (str op args)] ++ instrs

run : IO ()
run = do r <- sat $ solver [255] [0]
         case r of
           Nothing => do printLn "Error parsing result"
           Just (Sat, model) =>
              do putStrLn $ show model
                 putStrLn $ show $ parseInstrs model ops instrNames
                 pure ()
           Just (UnSat, _) => putStrLn "unsat"
           Just (Unknown, _) => putStrLn "unknown"
