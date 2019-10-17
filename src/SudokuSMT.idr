module SudokuSMT

import Data.Vect
import src.SMTLib
import src.Tensor



toTensor : Vect n (Vect n (Vect n (Vect n a))) -> Tensor [n, n, n, n] a
toTensor xs = Prism (Prism (Prism (Prism (Scalar xs))))

toVect : Tensor [n, n, n, n] a -> Vect n (Vect n (Vect n (Vect n a)))
toVect (Prism (Prism (Prism (Prism (Scalar xs))))) = xs

puzzle :  Vect 3 (Vect 3 (Vect 3 (Vect 3 Int)))
puzzle = [ [matrix00, matrix01, matrix02],
           [matrix10, matrix11, matrix12],
           [matrix20, matrix21, matrix22] ]
    where
      matrix00 : Vect 3 (Vect 3 Int)
      matrix00 = [ [5, 3, 0],
                   [6, 0, 0],
                   [0, 9, 8] ]
      matrix01 : Vect 3 (Vect 3 Int)
      matrix01 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix02 : Vect 3 (Vect 3 Int)
      matrix02 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix10 : Vect 3 (Vect 3 Int)
      matrix10 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix11 : Vect 3 (Vect 3 Int)
      matrix11 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix12 : Vect 3 (Vect 3 Int)
      matrix12 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix20 : Vect 3 (Vect 3 Int)
      matrix20 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix21 : Vect 3 (Vect 3 Int)
      matrix21 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix22 : Vect 3 (Vect 3 Int)
      matrix22 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]

vars : Vect 3 (Vect 3 (Vect 3 (Vect 3 String)))
vars = [ [ [ ["x_" ++ show i0 ++ "_" ++ show i1 ++ "_" ++ show i2 ++ "_" ++ show i3
             | i3 <- [0, 1, 2]]
             | i2 <- [0, 1, 2]]
             | i1 <- [0, 1, 2]]
             | i0 <- [0, 1, 2]]

cells : Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
cells ts with (toVect ts)
  cells ts | xs = ?vars_rhs

sudoku : Smt ()
sudoku = do vars <- declareVars (toTensor vars) (NumT IntT)
            assert $ cells vars
            end
