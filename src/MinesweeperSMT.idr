module MinesweeperSMT

import Data.Vect
import src.SMTLib
import src.Tensor


puzzle : Vect 3 (Vect 3 Int)
puzzle = [ [0, 1, -1],
           [0, 1, -1],
           [0, 0, 0] ]

shiftLeft : a -> Vect n a -> Vect n a
shiftLeft e [] = []
shiftLeft {n = S n} e (x :: xs) = replace {P = (\x => Vect x a)} (plusCommutative n 1) (xs ++ [e])

shiftRight : a -> Vect n a -> Vect n a
shiftRight e xs = reverse $ shiftLeft e $ reverse xs
