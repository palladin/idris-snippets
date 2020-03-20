module NQueensSMT

import Data.Vect
import src.SMTLib
import src.Tensor

N : Nat
N = 8

columns : Tensor [N] String
columns = toTensor $ tabulate (\i => "c_" ++ show (finToNat i))

rows : Tensor [N] String
rows = toTensor $ tabulate (\i => "r_" ++ show (finToNat i))

constrs : Vect N (Expr (NumT IntT)) -> Vect N (Expr (NumT IntT)) -> Expr BoolT
constrs cols rows = and [c >= (int 0) && c < (int (toIntNat N)) && r >= (int 0) && r < (int (toIntNat N)) | (c, r) <- zip cols rows] 

abs : Expr (NumT IntT) -> Expr (NumT IntT)
abs x = ite (x > (int 0)) x (x * (int (-1)))


solver : Smt ()
solver = do cols <- declareVars columns (NumT IntT)
            rows <- declareVars rows (NumT IntT)
            let cols = toVect cols
            let rows = toVect rows
            assert $ distinct cols
            assert $ distinct rows
            assert $ constrs cols rows
            checkSat
            getModel
            end


test : IO ()
test = print solver
