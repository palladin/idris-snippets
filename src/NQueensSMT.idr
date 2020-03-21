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

constrs : Vect n (Expr (NumT IntT)) -> Expr BoolT
constrs {n} xs = and [x >= (int 0) && x < (int (toIntNat n)) | x <- xs]


diags : Vect n (Expr (NumT IntT)) -> Vect n (Expr (NumT IntT)) -> Expr BoolT
diags [] [] = bool True
diags (col :: cols) (row :: rows) = let cs = map (\col' => abs $ col - col') cols in
                                    let rs = map (\row' => abs $ row - row') rows in
                                    let neqs = map (\(c, r) => not $ c == r) $ zip cs rs in
                                    and (diags cols rows :: neqs)
  where
    abs : Expr (NumT IntT) -> Expr (NumT IntT)
    abs x = ite (x >= (int 0)) x (x * (int (-1)))

solver : Smt ()
solver = do cols <- declareVars columns (NumT IntT)
            rows <- declareVars rows (NumT IntT)
            let cols = toVect cols
            let rows = toVect rows
            assert $ distinct cols
            assert $ distinct rows
            assert $ constrs cols
            assert $ constrs rows
            assert $ diags cols rows
            checkSat
            getModel
            end


test : IO ()
test = print solver
