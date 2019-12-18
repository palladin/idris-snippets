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
  isConst : Expr BoolT
  constVal : Expr (BitVecT size)
  val : Expr (BitVecT size)
  op : Expr (BitVecT size)
  args : Vect argsN (Arg size)

record InstrName (argsN : Nat) (size : Nat) where
    constructor MkInstrName
    pos : Nat
    isConst : String
    constVal : String
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

createInstrs : Vect n (Expr BoolT) -> Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Expr (BitVecT size)) -> Vect n (Vect argsN (Arg size)) -> Vect n (Instr argsN size)
createInstrs {size} isConsts constVals vals ops args = tabulate (\i => MkInstr (bv (finToInt i) size) (index i isConsts) (index i constVals) (index i vals) (index i ops) (index i args))

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
evalInstr {argsN} ops vars instrs = and [ite' (isConst instr) (val instr == constVal instr) (and [assocArg vars instrs instr, lookupOp (op instr) (val instr) (map val $ args instr) ops]) | instr <- instrs]
  where
    assocArg : Vect varsN (VarPos size) -> Vect instrsN (Instr argsN size) -> Instr argsN size -> Expr BoolT
    assocArg vars instrs instr = and $ tabulate (\i => let arg = index i (args instr) in ite' (isVar arg) (lookupVar (varPos arg) (val arg) vars)
                                                                                                         (lookupInstr (instrPos arg) (val arg) instrs))

VarsN : Nat
VarsN = 1

ArgsN : Nat
ArgsN = 2

OpsN : Nat
OpsN = 10

BitSize : Nat
BitSize = 32

ops : Vect OpsN (Op ArgsN BitSize)
ops = let ops = the (Vect OpsN (Op ArgsN BitSize))
                [MkOp 0 (\r, arg => r == bvand (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " & " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvor (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " | " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvnot (index 0 arg)) (\args => "~" ++ (index 0 args)),
                 MkOp 0 (\r, arg => ite' ((index 0 arg) == (index 1 arg)) (r == (bv 1 BitSize)) (r == (bv 0 BitSize))) (\args => (index 0 args) ++ " == " ++ (index 1 args) ++ " ? 1 : 0"),
                 MkOp 0 (\r, arg => r == bvsub (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " - " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvadd (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " + " ++ (index 1 args)),
                 --MkOp 0 (\r, arg => r == bvmul (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " * " ++ (index 1 args)),
                 --MkOp 0 (\r, arg => r == bvurem (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " % " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvshl (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " << " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvlshr (index 0 arg) (index 1 arg)) (\args => "(uint)" ++ (index 0 args) ++ " >> " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvashr (index 0 arg) (index 1 arg)) (\args => (index 0 args) ++ " >> " ++ (index 1 args)),
                 MkOp 0 (\r, arg => r == bvneg (index 0 arg)) (\args => "-" ++ (index 0 args))] in
      zipWith (\op, i =>  record { id = cast i } op) ops (fromList [0..OpsN - 1])

varPosVal : Int -> Tensor [VarsN] String
varPosVal n = varNames $ "varPosVal" ++ show n

argIsVar : Tensor [ArgsN, instrsN] String
argIsVar = varNames' "argIsVar"

argVarPos : Tensor [ArgsN, instrsN] String
argVarPos = varNames' "argVarPos"

argInstrPos : Tensor [ArgsN, instrsN] String
argInstrPos = varNames' "argInstrPos"

argVal : Int -> Tensor [ArgsN, instrsN] String
argVal n = varNames' $ "argVal" ++ show n

instrVal : Int -> Tensor [instrsN] String
instrVal n = varNames $ "instrVal" ++ show n

instrOp : Tensor [instrsN] String
instrOp = varNames "instrOp"

instrIsConst : Tensor [instrsN] String
instrIsConst = varNames "isConst"

instrConstVal : Tensor [instrsN] String
instrConstVal = varNames "constVal"

instrNames : Vect instrsN (InstrName ArgsN BitSize)
instrNames = tabulate (\i => MkInstrName (finToNat i)
                                         (index i (toVect instrIsConst))
                                         (index i (toVect instrConstVal))
                                         (index i (toVect instrOp))
                                         (tabulate (\j => MkArgName (index i j (toVect argIsVar))
                                                                    (index i j (toVect argVarPos))
                                                                    (index i j (toVect argInstrPos)))))

eval : {prf : GTE instrsN 1} -> Int -> List (Expr (BitVecT BitSize), Expr (BitVecT BitSize) -> Expr BoolT) ->
       Tensor [ArgsN, instrsN] (Expr BoolT) -> Tensor [ArgsN, instrsN] (Expr (BitVecT BitSize)) ->
       Tensor [ArgsN, instrsN] (Expr (BitVecT BitSize)) -> Tensor [instrsN] (Expr (BitVecT BitSize)) ->
       Tensor [instrsN] (Expr BoolT) -> Tensor [instrsN] (Expr (BitVecT BitSize)) -> Smt ()
eval {instrsN} {prf} n [] argIsVar argVarPos argInstrPos instrOp instrIsConst instrConstVal = pure ()
eval {instrsN = S instrsN'} {prf = (LTESucc LTEZero)} n ((inp, outf) :: xs) argIsVar argVarPos argInstrPos instrOp instrIsConst instrConstVal =
    do vars <- declareVars (varPosVal n) (BitVecT BitSize)
       argVal <- declareVars (argVal {instrsN = S instrsN'} n) (BitVecT BitSize)
       instrVal <- declareVars (instrVal {instrsN = S instrsN'} n) (BitVecT BitSize)
       let vps = createVarPos (toVect vars)
       let args = createArgs (toVect argIsVar) (toVect argVarPos) (toVect argInstrPos) (toVect argVal)
       let instrs = createInstrs (toVect instrIsConst) (toVect instrConstVal) (toVect instrVal) (toVect instrOp) args
       assert $ evalInstr ops vps instrs
       assert $ val (index 0 vps) == inp
       r <- declareVar ("output" ++ show n) (BitVecT BitSize)
       assert $ outf r
       assert $ val (index 0 instrs) == r
       eval {prf = (LTESucc LTEZero)} (n + 1) xs argIsVar argVarPos argInstrPos instrOp instrIsConst instrConstVal
       pure ()

solver : {instrsN : Nat} -> {prf : GTE instrsN 1} -> List (Expr (BitVecT BitSize), Expr (BitVecT BitSize) -> Expr BoolT) -> Smt ()
solver {instrsN} {prf} xs =
         do setLogic "QF_BV"
            setOption ":timeout 120000"
            setOption ":parallel.enable true"
            setOption ":pp.bv-literals false"
            let n = 0
            argIsVar <- declareVars (argIsVar {instrsN = instrsN}) BoolT
            argVarPos <- declareVars (argVarPos {instrsN = instrsN}) (BitVecT BitSize)
            argInstrPos <- declareVars (argInstrPos {instrsN = instrsN}) (BitVecT BitSize)
            instrOp <- declareVars (instrOp {instrsN = instrsN}) (BitVecT BitSize)
            instrIsConst <- declareVars (instrIsConst {instrsN = instrsN}) BoolT
            instrConstVal <- declareVars (instrConstVal {instrsN = instrsN}) (BitVecT BitSize)
            vars <- declareVars (varPosVal n) (BitVecT BitSize)
            argVal <- declareVars (argVal {instrsN = instrsN} n) (BitVecT BitSize)
            instrVal <- declareVars (instrVal {instrsN = instrsN} n) (BitVecT BitSize)
            let vps = createVarPos (toVect vars)
            let args = createArgs (toVect argIsVar) (toVect argVarPos) (toVect argInstrPos) (toVect argVal)
            let instrs = createInstrs (toVect instrIsConst) (toVect instrConstVal) (toVect instrVal) (toVect instrOp) args
            assert $ checkInstr instrs
            eval {prf = prf} (n + 1) xs argIsVar argVarPos argInstrPos instrOp instrIsConst instrConstVal
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
parseInstrs model ops [] = Just []
parseInstrs model ops ((MkInstrName pos isConst constVal opStr args) :: instrs) =
    do isConst <- lookup isConst model
       isConst <- parseBool isConst
       constVal <- lookup constVal model
       case isConst of
         True =>
          do args <- parseArgs model args
             instrs <- parseInstrs model ops instrs
             pure $ ["int instr" ++ show pos ++ " = " ++ constVal ++ ";"] ++ instrs
         False =>
           do opVal <- lookup opStr model
              opId <- parseInteger {a = Int} opVal
              op <- find (\op => id op == opId) ops
              args <- parseArgs model args
              instrs <- parseInstrs model ops instrs
              pure $ ["int instr" ++ show pos ++ " = " ++ (str op args) ++ ";"] ++ instrs

equiv : Vect n (Expr a) -> Expr a -> Expr a -> (Expr a -> Vect n (Expr a) -> Expr BoolT) -> (Expr a -> Vect n (Expr a) -> Expr BoolT) -> Expr BoolT
equiv xs r r' f g = and [f r xs, g r' xs, not $ r == r']

testEquiv : Smt ()
testEquiv = let size = 64 in
            do setLogic "QF_BV"
               setOption ":pp.bv-literals false"
               xs <- declareVars {f = Vect 3} ["a", "b", "c"] (BitVecT size)
               r <- declareVar "r" (BitVecT size)
               r' <- declareVar "_r" (BitVecT size)
               assert $ equiv xs r r' (\r, xs => r == ((((index 0 xs) `bvmul` (index 0 xs)) `bvmul` (index 0 xs)) `bvadd` (((index 1 xs) `bvmul` (index 1 xs)) `bvmul` (index 1 xs))))
                                      (\r, xs => r == (((index 2 xs) `bvmul` (index 2 xs)) `bvmul` (index 2 xs)))
               checkSat
               getModel
               end

runEquiv : IO ()
runEquiv = do r <- sat testEquiv
              case r of
                Nothing => do putStrLn "Error parsing result"
                Just (Sat, model) =>
                   do
                      putStrLn "sat"
                      putStrLn $ show model
                      pure ()
                Just (UnSat, _) => putStrLn "unsat"
                Just (Unknown, _) => putStrLn "unknown"


data' : List (Expr (BitVecT BitSize), Expr (BitVecT BitSize) -> Expr BoolT)
data' = let inp = example in
        map (\(a, b) => (bv a BitSize, \r => r == bv b BitSize)) inp
  where
    isPowerOfTwo : List (Int, Int)
    isPowerOfTwo = [(2, 1), (3, 0), (4, 1), (5, 0), (6, 0), (8, 1)]
    isEven : List (Int, Int)
    isEven = [(2, 1), (3, 0), (4, 1), (5, 0), (6, 1), (7, 0)]
    primes : List (Int, Int)
    primes = [(2, 3), (3, 5), (5, 7), (7, 11), (11, 13), (17, 19), (19, 23)]
    example : List (Int, Int)
    example = [(1, 1), (2, 2), (5, 1000), (6, 6)]

runSolver : (instrsN : Nat) -> {prf : GTE instrsN 1} -> IO ()
runSolver instrsN {prf} = do r <- sat $ solver {prf = prf} data'
                             --putStrLn $ "model: " ++ show r
                             case r of
                               Nothing => do putStrLn "Error parsing result"
                               Just (Sat, model) =>
                                  case parseInstrs {n = instrsN} model ops instrNames of
                                    Just instrs =>
                                      do putStrLn $ unlines $ reverse $ instrs
                                         pure ()
                                    Nothing => do putStrLn "Error parsing instrs"
                               Just (UnSat, _) => putStrLn "unsat"
                               Just (Unknown, _) => putStrLn "unknown"


run : (n : Nat) -> (instrsN : Nat) -> {auto prf : GTE instrsN 1} -> IO ()
run Z instrsN {prf = prf} = pure ()
run (S n) instrsN {prf = prf} = do putStrLn $ "n instrs: " ++ show instrsN
                                   runSolver {prf = prf} instrsN
                                   run n (S instrsN)
