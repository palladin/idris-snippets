module SudokuSMT

import Data.Vect
import src.SMTLib
import src.Tensor


puzzle :  Tensor [3, 3, 3, 3] Int
puzzle = toTensor
           [ [matrix00, matrix01, matrix02],
             [matrix10, matrix11, matrix12],
             [matrix20, matrix21, matrix22] ]
    where
      matrix00 : Vect 3 (Vect 3 Int)
      matrix00 = [ [5, 3, 0],
                   [6, 0, 0],
                   [0, 9, 8] ]
      matrix01 : Vect 3 (Vect 3 Int)
      matrix01 = [ [0, 7, 0],
                   [1, 9, 5],
                   [0, 0, 0] ]
      matrix02 : Vect 3 (Vect 3 Int)
      matrix02 = [ [0, 0, 0],
                   [0, 0, 0],
                   [0, 6, 0] ]
      matrix10 : Vect 3 (Vect 3 Int)
      matrix10 = [ [8, 0, 0],
                   [4, 0, 0],
                   [7, 0, 0] ]
      matrix11 : Vect 3 (Vect 3 Int)
      matrix11 = [ [0, 6, 0],
                   [8, 0, 3],
                   [0, 2, 0] ]
      matrix12 : Vect 3 (Vect 3 Int)
      matrix12 = [ [0, 0, 3],
                   [0, 0, 1],
                   [0, 0, 6] ]
      matrix20 : Vect 3 (Vect 3 Int)
      matrix20 = [ [0, 6, 0],
                   [0, 0, 0],
                   [0, 0, 0] ]
      matrix21 : Vect 3 (Vect 3 Int)
      matrix21 = [ [0, 0, 0],
                   [4, 1, 9],
                   [0, 8, 0] ]
      matrix22 : Vect 3 (Vect 3 Int)
      matrix22 = [ [2, 8, 0],
                   [0, 0, 5],
                   [0, 7, 9] ]

vars : Tensor [3, 3, 3, 3] String
vars = toTensor
        [ [ [ ["x_" ++ show i0 ++ "_" ++ show i1 ++ "_" ++ show i2 ++ "_" ++ show i3
             | i3 <- [0, 1, 2]]
             | i2 <- [0, 1, 2]]
             | i1 <- [0, 1, 2]]
             | i0 <- [0, 1, 2]]

cells : Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
cells ts with (toVect ts)
  cells ts | xssss = let xs = concat $ concat $ concat xssss in
                    and $ map (\x => (int 1) <= x && x <= (int 9)) xs

rows : Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
rows ts with (toVect ts)
  rows ts | xssss = let rs = concat $ map zipRows xssss in
                    and $ map distinct rs
  where
    zipRows : Vect 3 (Vect 3 (Vect 3 (Expr (NumT IntT)))) -> Vect 3 (Vect 9 (Expr (NumT IntT)))
    zipRows xsss = zipWith3 (\xs, ys, zs => xs ++ ys ++ zs) (index 0 xsss) (index 1 xsss) (index 2 xsss)

cols : Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
cols ts with (toVect ts)
  cols ts | xssss = let rs = concat $ map zipCols $ map (map transpose) $ transpose xssss in
                        and $ map distinct rs
  where
    zipCols : Vect 3 (Vect 3 (Vect 3 (Expr (NumT IntT)))) -> Vect 3 (Vect 9 (Expr (NumT IntT)))
    zipCols xsss = zipWith3 (\xs, ys, zs => xs ++ ys ++ zs) (index 0 xsss) (index 1 xsss) (index 2 xsss)

square : Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
square ts with (toVect ts)
  square ts | xssss = and $ map (\xss => distinct (concat xss)) $ concat xssss

instanceCheck : Tensor [3, 3, 3, 3] Int -> Tensor [3, 3, 3, 3] (Expr (NumT IntT)) -> Expr BoolT
instanceCheck insts vars with (toVect insts, toVect vars)
  instanceCheck insts vars | (insts', vars') = let insts'' = concat $ concat $ concat insts' in
                                               let vars'' = concat $ concat $ concat vars' in
                                               and $ zipWith (\inst, var => ite ((int inst) == (int 0)) (bool True) ((int inst) == var)) insts'' vars''

sudoku : Smt ()
sudoku = do vars <- declareVars vars (NumT IntT)
            assert $ cells vars
            assert $ rows vars
            assert $ cols vars
            assert $ square vars
            assert $ instanceCheck puzzle vars
            checkSat
            getModel
            end

test : IO ()
test = print sudoku
