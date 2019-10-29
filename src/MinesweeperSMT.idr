module MinesweeperSMT

import Data.Vect
import src.SMTLib
import src.Tensor


puzzle : Vect 9 (Vect 9 Int)
puzzle = [ [-1, -1, -1, -1,  1,  0,  0,  1, -1],
           [-1, -1,  2,  1,  1,  0,  0,  1,  1],
           [-1, -1,  1,  0,  0,  0,  0,  0,  0],
           [-1,  2,  1,  0,  0,  0,  0,  0,  0],
           [-1,  2,  0,  0,  0,  0,  0,  0,  0],
           [-1,  3,  1,  0,  0,  0,  1,  1,  1],
           [-1, -1,  1,  0,  0,  0,  1, -1, -1],
           [-1, -1,  2,  2,  1,  1,  1, -1, -1],
           [-1, -1, -1, -1, -1, -1, -1, -1, -1] ]

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

lookup : Fin n -> Fin m -> List Dir ->  Vect n (Vect m (Expr (NumT IntT))) -> Expr (NumT IntT)
lookup n m ds xss = index n m $ shift ds (int 0) xss

equation : Fin n -> Fin m -> Int -> Vect n (Vect m (Expr (NumT IntT))) -> Expr BoolT
equation n m v xss with (toPos n, toPos m)
  equation n m v xss | (First, First) = add [lookup n m [Left] xss, lookup n m [Up] xss, lookup n m [Up, Left] xss] == (int v)
  equation n m v xss | (Last, Last) = add [lookup n m [Right] xss, lookup n m [Down] xss, lookup n m [Down, Right] xss] == (int v)
  equation n m v xss | (First, Last) = add [lookup n m [Right] xss, lookup n m [Up] xss, lookup n m [Up, Right] xss] == (int v)
  equation n m v xss | (Last, First) = add [lookup n m [Left] xss, lookup n m [Down] xss, lookup n m [Down, Left] xss] == (int v)
  equation n m v xss | (First, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Up] xss,
                                         lookup n m [Up, Right] xss, lookup n m [Up, Left] xss] == (int v)
  equation n m v xss | (Last, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Down] xss,
                                        lookup n m [Down, Right] xss, lookup n m [Down, Left] xss] == (int v)
  equation n m v xss | (_, First) = add [lookup n m [Left] xss, lookup n m [Down] xss, lookup n m [Down, Left] xss,
                                         lookup n m [Up] xss, lookup n m [Up, Left] xss] == (int v)
  equation n m v xss | (_, Last) = add [lookup n m [Right] xss, lookup n m [Down] xss, lookup n m [Down, Right] xss,
                                        lookup n m [Up] xss, lookup n m [Up, Right] xss] == (int v)
  equation n m v xss | (_, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Down] xss,
                                     lookup n m [Up] xss, lookup n m [Down, Right] xss, lookup n m [Down, Left] xss,
                                     lookup n m [Up, Right] xss, lookup n m [Up, Left] xss] == (int v)

collect : Vect n (Vect m Int) -> Vect n (Vect m (Expr (NumT IntT))) -> Vect n (Vect m (Expr BoolT))
collect puzzle vars = tabulate (\n => tabulate (\m => let (x, v) = (index n m puzzle, index n m vars) in
                                                      if x < 0 then (v == (int 0)) || (v == (int 1)) else (v == (int 0)) && equation n m x vars))

vars : Tensor [9, 9] String
vars = toTensor $ tabulate (\i0 => tabulate (\i1 => "x_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

inst : Vect 9 (Vect 9 (Expr (NumT IntT)))
inst = tabulate (\i0 => tabulate (\i1 => int $ index i0 i1 puzzle))

solver : Smt ()
solver = do vars <- declareVars vars (NumT IntT)
            assert $ and $ concat $ collect puzzle (toVect vars)
            assert $ index 0 1 (toVect vars) == (int 1)
            checkSat
            getModel
            end

test : IO ()
test = print solver
