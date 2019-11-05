module LifeSMT

import Data.Vect
import src.SMTLib
import src.Tensor


pattern : Vect 7 (Vect 15 Int)
pattern = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0],
           [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
           [0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0],
           [0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
           [0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0],
           [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]


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

countNeighborhoods : Fin n -> Fin m -> Vect n (Vect m (Expr (NumT IntT))) -> Expr (NumT IntT)
countNeighborhoods n m xss with (toPos n, toPos m)
 countNeighborhoods n m xss | (First, First) = add [lookup n m [Left] xss, lookup n m [Up] xss, lookup n m [Up, Left] xss]
 countNeighborhoods n m xss | (Last, Last) = add [lookup n m [Right] xss, lookup n m [Down] xss, lookup n m [Down, Right] xss]
 countNeighborhoods n m xss | (First, Last) = add [lookup n m [Right] xss, lookup n m [Up] xss, lookup n m [Up, Right] xss]
 countNeighborhoods n m xss | (Last, First) = add [lookup n m [Left] xss, lookup n m [Down] xss, lookup n m [Down, Left] xss]
 countNeighborhoods n m xss | (First, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Up] xss,
                                                lookup n m [Up, Right] xss, lookup n m [Up, Left] xss]
 countNeighborhoods n m xss | (Last, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Down] xss,
                                               lookup n m [Down, Right] xss, lookup n m [Down, Left] xss]
 countNeighborhoods n m xss | (_, First) = add [lookup n m [Left] xss, lookup n m [Down] xss, lookup n m [Down, Left] xss,
                                                lookup n m [Up] xss, lookup n m [Up, Left] xss]
 countNeighborhoods n m xss | (_, Last) = add [lookup n m [Right] xss, lookup n m [Down] xss, lookup n m [Down, Right] xss,
                                               lookup n m [Up] xss, lookup n m [Up, Right] xss]
 countNeighborhoods n m xss | (_, _) = add [lookup n m [Left] xss, lookup n m [Right] xss, lookup n m [Down] xss,
                                            lookup n m [Up] xss, lookup n m [Down, Right] xss, lookup n m [Down, Left] xss,
                                            lookup n m [Up, Right] xss, lookup n m [Up, Left] xss]

initBoard : Tensor [7, 15] String
initBoard = toTensor $ tabulate (\i0 => tabulate (\i1 => "x_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))


solver : Smt ()
solver = do initBoard <- declareVars initBoard (NumT IntT)
            assert $ countNeighborhoods 0 0 (toVect initBoard) == (int 0)
            checkSat
            getModel
            end

test : IO ()
test = print solver
