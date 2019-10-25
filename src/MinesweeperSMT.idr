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

data Pos = First | Last | Middle

toPos : Fin n -> Pos
toPos {n} fin with (finToNat fin)
  toPos {n} fin | Z = First
  toPos {n} fin | n' = if n == (S n') then Last else Middle

collect : Fin n -> Fin m -> Vect n (Vect m Int) -> Expr BoolT
collect {n} {m} fn fm xss with (toPos fn, toPos fm)
  collect {n} {m} fn fm xss | (First, First) = let r = index fn fm (map (shiftLeft 0) xss) in
                                               let d = index fn fm (shiftLeft (replicate _ 0) xss) in
                                               let dr = index fn fm (map (shiftLeft 0) (shiftLeft (replicate _ 0) xss)) in
                                               and [((int r) == (int d)), ((int dr) == (int dr))]
  collect {n} {m} fn fm xss | (Last, Last) = let l = index fn fm (map (shiftRight 0) xss) in
                                             let u = index fn fm (shiftRight (replicate _ 0) xss) in
                                             let ul = index fn fm (map (shiftRight 0) (shiftRight (replicate _ 0) xss)) in
                                             and [((int l) == (int u)), ((int ul) == (int ul))]
  collect {n} {m} fn fm xss | (_, _) = let r = index fn fm (map (shiftLeft 0) xss) in
                                       let l = index fn fm (map (shiftRight 0) xss) in
                                       let u = index fn fm (shiftRight (replicate _ 0) xss) in
                                       let d = index fn fm (shiftLeft (replicate _ 0) xss) in
                                       let ul = index fn fm (map (shiftRight 0) (shiftRight (replicate _ 0) xss)) in
                                       let ur = index fn fm (map (shiftLeft 0) (shiftRight (replicate _ 0) xss)) in
                                       let dl = index fn fm (map (shiftRight 0) (shiftLeft (replicate _ 0) xss)) in
                                       let dr = index fn fm (map (shiftLeft 0) (shiftLeft (replicate _ 0) xss)) in
                                       and [((int l) == (int r)), ((int u) == (int d)), ((int ul) == (int ur)), ((int dl) == (int dr))]
