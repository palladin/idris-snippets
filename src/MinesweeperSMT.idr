module MinesweeperSMT

import Data.Vect
import src.SMTLib
import src.Tensor


puzzle : Vect 3 (Vect 3 Int)
puzzle = [ [1, 2, 3],
           [4, 5, 6],
           [7, 8, 9] ]

shiftLeft : a -> Vect n a -> Vect n a
shiftLeft e [] = []
shiftLeft {n = S n} e (x :: xs) = replace {P = (\x => Vect x a)} (plusCommutative n 1) (xs ++ [e])

shiftRight : a -> Vect n a -> Vect n a
shiftRight e xs = reverse $ shiftLeft e $ reverse xs

index : Fin n -> Fin m -> Vect n (Vect m a) -> a
index n m xss = index m (index n xss)

collect : Fin n -> Fin m -> Vect n (Vect m Int) -> Expr BoolT
collect n m xss = let r = (index n m (map (shiftLeft 0) xss)) in
                  let l = (index n m (map (shiftRight 0) xss)) in
                  (int l) == (int r)
