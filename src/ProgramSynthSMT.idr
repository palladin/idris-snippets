module ProgramSynthSMT


import Data.Vect
import src.SMTLib
import src.Tensor


record VarPos (n : Nat) where
    constructor MkVar
    pos : Expr (BitVecT n)
    var : Expr (BitVecT n)

assocVarPos : Vect n (Expr (BitVecT size)) -> Vect n (VarPos size)
assocVarPos {n} {size} vs = tabulate (\i => MkVar (bv (finToInt i) size) (index i vs))

lookupVar : Expr (BitVecT size) -> Expr (BitVecT size) -> Vect n (VarPos size) -> Expr BoolT
lookupVar p v vs = or [ite (p == pos v') (v == var v') (bool False) | v' <- vs]

varNames : String -> Tensor [n] String
varNames name = toTensor $ tabulate (\i => name ++ "_" ++ show (finToNat i))

solver : Smt ()
solver = do setOption ":pp.bv-literals false"
            vars <- declareVars (varNames "var" {n = 2}) (BitVecT 8)
            let vars = toVect vars
            let vps = assocVarPos vars
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
