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

data Dir = Left | Right | Up | Down

shift : List Dir -> a -> Vect n (Vect m a) -> Vect n (Vect m a)
shift [] e xss = xss
shift (Left :: ds) e xss = shift ds e (map (shiftLeft e) xss)
shift (Right :: ds) e xss = shift ds e (map (shiftRight e) xss)
shift (Up :: ds) e xss = shift ds e (shiftLeft (replicate _ e) xss)
shift (Down :: ds) e xss = shift ds e (shiftRight (replicate _ e) xss)

index : Fin n -> Fin m -> Vect n (Vect m a) -> a
index n m xss = index m (index n xss)

data Pos = First | Last | Middle

toPos : Fin n -> Pos
toPos {n} fin with (finToNat fin)
  toPos {n} fin | Z = First
  toPos {n} fin | n' = if n == (S n') then Last else Middle

collect : Fin n -> Fin m -> Int -> Vect n (Vect m (Expr (NumT IntT))) -> Expr BoolT
collect n m v xss with (toPos n, toPos m)
  collect n m v xss | (First, First) = let r = index n m $ shift [Left] (int 0) xss in
                                       let d = index n m $ shift [Up] (int 0) xss in
                                       let dr = index n m $ shift [Up, Left] (int 0) xss in
                                       add [r, d, dr] == (int v)
  collect n m v xss | (Last, Last) = let l = index n m $ shift [Right] (int 0) xss in
                                     let u = index n m $ shift [Down] (int 0) xss in
                                     let ul = index n m $ shift [Down, Right] (int 0) xss in
                                     add [l, u, ul] == (int v)
  collect n m v xss | (_, _) = let r = index n m $ shift [Left] (int 0) xss in
                               let l = index n m $ shift [Right] (int 0) xss in
                               let u = index n m $ shift [Down] (int 0) xss in
                               let d = index n m $ shift [Up] (int 0) xss in
                               let ul = index n m $ shift [Down, Right] (int 0) xss in
                               let ur = index n m $ shift [Down, Left] (int 0) xss in
                               let dl = index n m $ shift [Up, Right] (int 0) xss in
                               let dr = index n m $ shift [Up, Left] (int 0) xss in
                               add [r, l, u, d, ul, ur, dl, dr] == (int v)


vars : Tensor [3, 3] String
vars = toTensor [ [ "x_" ++ show i0 ++ "_" ++ show i1 | i1 <- [0, 1, 2]] | i0 <- [0, 1, 2]]

inst : Vect 3 (Vect 3 (Expr (NumT IntT)))
inst = tabulate (\i0 => tabulate (\i1 => int $ index i0 i1 puzzle))

solver : Smt ()
solver = do vars <- declareVars vars (NumT IntT)
            assert $ collect 0 0 1 (toVect vars)
            checkSat
            getModel
            end
