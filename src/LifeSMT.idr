module LifeSMT

import Data.Vect
import src.SMTLib
import src.Tensor


pattern0 : Vect 6 (Vect 6 Int)
pattern0 = [[0, 0, 0, 0, 0, 0],
            [0, 0, 1, 0, 0, 0],
            [0, 0, 0, 1, 0, 0],
            [0, 1, 1, 1, 0, 0],
            [0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0]]

pattern1 : Vect 6 (Vect 6 Int)
pattern1 = [[0, 0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0, 0],
            [0, 1, 0, 1, 0, 0],
            [0, 0, 1, 1, 0, 0],
            [0, 0, 1, 0, 0, 0],
            [0, 0, 0, 0, 0, 0]]


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

rules : Vect n (Vect m (Expr (NumT IntT))) -> Vect n (Vect m (Expr (NumT IntT))) -> Vect n (Vect m (Expr (NumT IntT))) -> Expr BoolT
rules counters fromBoard toBoard = and $ concat $ tabulate (\i0 => tabulate (\i1 => rule i0 i1 counters fromBoard toBoard))
  where
    rule : Fin n -> Fin m -> Vect n (Vect m (Expr (NumT IntT))) -> Vect n (Vect m (Expr (NumT IntT))) -> Vect n (Vect m (Expr (NumT IntT))) -> Expr BoolT
    rule n m counters fromBoard toBoard = let c = index n m counters in
                                          let eqc = countNeighborhoods n m fromBoard == c in
                                          let from = index n m fromBoard in
                                          let eqf = from == (int 0) || from == (int 1) in
                                          let to = index n m toBoard in
                                          let eqt = to == (int 0) || to == (int 1) in
                                          let r = ite (from == (int 1))
                                                    (ite (c == (int 0) || c == (int 1))
                                                      (to == (int 0))
                                                      (ite (or [c == (int 4), c == (int 5), c == (int 6),
                                                                c == (int 7), c == (int 8)])
                                                        (to == (int 0))
                                                        (ite (or [c == (int 2), c == (int 3)])
                                                          (to == (int 1))
                                                          (bool False))))
                                                    (ite (c == (int 3))
                                                      (to == (int 1))
                                                      (to == (int 0))) in
                                          and [eqc, eqf, eqt, r]

validPattern : Vect n (Vect m Int) -> Vect n (Vect m (Expr (NumT IntT))) -> Expr BoolT
validPattern pattern board = and $ concat $ tabulate (\i0 => tabulate (\i1 => index i0 i1 board == (int $ index i0 i1 pattern)))

initBoard : Tensor [6, 6] String
initBoard = toTensor $ tabulate (\i0 => tabulate (\i1 => "x_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

finalBoard : Tensor [6, 6] String
finalBoard = toTensor $ tabulate (\i0 => tabulate (\i1 => "y_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))

counters : Tensor [6, 6] String
counters = toTensor $ tabulate (\i0 => tabulate (\i1 => "c_" ++ show (finToNat i0) ++ "_" ++ show (finToNat i1)))


solver : Smt ()
solver = do initBoard <- declareVars initBoard (NumT IntT)
            finalBoard <- declareVars finalBoard (NumT IntT)
            counters <- declareVars counters (NumT IntT)
            assert $ rules (toVect counters) (toVect initBoard) (toVect finalBoard)
            assert $ validPattern pattern1 (toVect finalBoard)
            checkSat
            getModel
            end

test : IO ()
test = print solver
