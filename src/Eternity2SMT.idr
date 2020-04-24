module Eternity2SMT

import Data.String
import Data.Vect
import src.SMTLib
import src.Tensor
import src.GridOps

Dim : Nat
Dim = 4

E : Nat
E = 4

BitSize : Nat
BitSize = 8

ColorBitSize : Nat
ColorBitSize = 5

record Piece where
 constructor MkPiece
 up : Char
 right : Char
 down : Char
 left : Char

record PieceColors (size : Nat) where
 constructor MkPieceColors
 upVar : Expr (BitVecT size)
 rightVar : Expr (BitVecT size)
 downVar : Expr (BitVecT size)
 leftVar : Expr (BitVecT size)

puzzle : Vect (Dim * Dim) (Vect E Char)
puzzle = [ ['Y', 'X', 'X', 'B'], ['Y', 'B', 'X', 'X'], ['X', 'B', 'B', 'X'], ['X', 'Y', 'Y', 'X'],
           ['U', 'U', 'U', 'P'], ['P', 'U', 'P', 'P'], ['U', 'U', 'P', 'P'], ['U', 'U', 'P', 'P'],
           ['Y', 'X', 'Y', 'P'], ['B', 'X', 'B', 'P'], ['Y', 'X', 'B', 'P'], ['B', 'X', 'Y', 'P'],
           ['Y', 'X', 'Y', 'U'], ['B', 'X', 'B', 'U'], ['B', 'X', 'Y', 'U'], ['Y', 'X', 'B', 'U'] ]

data Lookup : (a : Type) -> Fin n -> Fin m -> Vect n (Vect m a) -> Type where
 FF : a -> a -> Lookup a n m xs
 LL : a -> a -> Lookup a n m xs
 FL : a -> a -> Lookup a n m xs
 LF : a -> a -> Lookup a n m xs
 FM : a -> a -> a -> Lookup a n m xs
 LM : a -> a -> a -> Lookup a n m xs
 MF : a -> a -> a -> Lookup a n m xs
 ML : a -> a -> a -> Lookup a n m xs
 M : a -> a -> a -> a -> Lookup a n m xs

toLookup : (fn : Fin n) -> (fm : Fin m) -> a -> (xs : Vect n (Vect m a)) -> Lookup a fn fm xs
toLookup i j x xs with (toPos i, toPos j)
 toLookup i j x xs | (First, First) = FF (lookup i j [Left] x xs) (lookup i j [Up] x xs)
 toLookup i j x xs | (Last, Last) = LL (lookup i j [Down] x xs) (lookup i j [Right] x xs)
 toLookup i j x xs | (First, Last) = FL (lookup i j [Up] x xs) (lookup i j [Right] x xs)
 toLookup i j x xs | (Last, First) = LF (lookup i j [Down] x xs) (lookup i j [Left] x xs)
 toLookup i j x xs | (First, _) = FM (lookup i j [Left] x xs) (lookup i j [Up] x xs) (lookup i j [Right] x xs)
 toLookup i j x xs | (Last, _) = LM (lookup i j [Down] x xs) (lookup i j [Left] x xs) (lookup i j [Right] x xs)
 toLookup i j x xs | (_, First) = MF (lookup i j [Down] x xs) (lookup i j [Left] x xs) (lookup i j [Up] x xs)
 toLookup i j x xs | (_, Last) = ML (lookup i j [Down] x xs) (lookup i j [Up] x xs) (lookup i j [Right] x xs)
 toLookup i j x xs | (_, _) = M (lookup i j [Down] x xs) (lookup i j [Left] x xs) (lookup i j [Up] x xs) (lookup i j [Right] x xs)



colorInt : Char -> Int
colorInt c = cast c - cast 'A'

intColor : Int -> Char
intColor i = cast $ cast 'A' + i

rotate : Vect n a -> Vect n a
rotate {n = Z} [] = []
rotate {n = (S n)} (x :: xs) = let rs = xs ++ [x] in
                               replace {P = (\x => Vect x a)} (plusCommutative n 1) rs

rotations : Vect E Char -> Vect E Piece
rotations p = let p' = rotate p in
              let p'' = rotate p' in
              let p''' = rotate p'' in
              let f = \p => MkPiece (index 0 p) (index 1 p) (index 2 p) (index 3 p) in
              [ f p, f p', f p'', f p''' ]

pieces : Vect (Dim * Dim) (Int, Vect E Piece)
pieces = tabulate (\i => (finToInt i, rotations $ index i puzzle))

varPieces : Tensor [Dim, Dim] String
varPieces = toTensor $ tabulate (\i => tabulate (\j => "x_" ++ show (finToNat i) ++ "_" ++ show (finToNat j)))

varColorPieces : Tensor [Dim, Dim, E] String
varColorPieces = toTensor $ tabulate (\i => tabulate (\j => ["cx_" ++ show (finToNat i) ++ "_" ++ show (finToNat j) ++ "_Up",
                                                             "cx_" ++ show (finToNat i) ++ "_" ++ show (finToNat j) ++ "_Right",
                                                             "cx_" ++ show (finToNat i) ++ "_" ++ show (finToNat j) ++ "_Down",
                                                             "cx_" ++ show (finToNat i) ++ "_" ++ show (finToNat j) ++ "_Left"]))

mapColorPieces : Vect Dim (Vect Dim (Vect E (Expr (BitVecT ColorBitSize)))) -> Vect Dim (Vect Dim (PieceColors ColorBitSize))
mapColorPieces vs = tabulate (\i => tabulate (\j => MkPieceColors (index 0 $ index j $ index i vs) (index 1 $ index j $ index i vs)
                                                                  (index 2 $ index j $ index i vs) (index 3 $ index j $ index i vs)))

equalColors : Piece -> PieceColors ColorBitSize -> Expr BoolT
equalColors p pc = and [bv (colorInt $ up p) ColorBitSize == upVar pc,
                        bv (colorInt $ right p) ColorBitSize == rightVar pc,
                        bv (colorInt $ down p) ColorBitSize == downVar pc,
                        bv (colorInt $ left p) ColorBitSize == leftVar pc]

validPieces : Vect Dim (Vect Dim (Expr (BitVecT BitSize))) -> Expr BoolT
validPieces varPieces = and $ concat $ tabulate (\i => tabulate (\j => bvuge (index i j varPieces) (bv 0 BitSize) && bvult (index i j varPieces) (bv (toIntNat $ Dim * Dim) BitSize)))

dummy : PieceColors ColorBitSize
dummy = MkPieceColors (bv 0 ColorBitSize) (bv 0 ColorBitSize) (bv 0 ColorBitSize) (bv 0 ColorBitSize)


colorConstraint : Fin Dim -> Fin Dim -> Vect Dim (Vect Dim (PieceColors ColorBitSize)) -> Expr BoolT
colorConstraint i j pcs with (index i j pcs, toLookup i j dummy pcs)
  colorConstraint i j pcs | (pc, (FF r d)) = and [upVar pc == bv (colorInt 'X') ColorBitSize,
                                                  leftVar pc == bv (colorInt 'X') ColorBitSize,
                                                  rightVar pc == leftVar r, downVar pc == upVar d]
  colorConstraint i j pcs | (pc, (LL u l)) = and [downVar pc == bv (colorInt 'X') ColorBitSize,
                                                  rightVar pc == bv (colorInt 'X') ColorBitSize,
                                                  upVar pc == downVar u, leftVar pc == rightVar l]
  colorConstraint i j pcs | (pc, (FL d l)) = and [upVar pc == bv (colorInt 'X') ColorBitSize,
                                                  rightVar pc == bv (colorInt 'X') ColorBitSize,
                                                  downVar pc == upVar d, leftVar pc == rightVar l]
  colorConstraint i j pcs | (pc, (LF u r)) = and [downVar pc == bv (colorInt 'X') ColorBitSize,
                                                  leftVar pc == bv (colorInt 'X') ColorBitSize,
                                                  upVar pc == downVar u, rightVar pc == leftVar r]
  colorConstraint i j pcs | (pc, (FM r d l)) = and [upVar pc == bv (colorInt 'X') ColorBitSize,
                                                    downVar pc == upVar d, leftVar pc == rightVar l, rightVar pc == leftVar r]
  colorConstraint i j pcs | (pc, (LM u r l)) = and [downVar pc == bv (colorInt 'X') ColorBitSize,
                                                    upVar pc == downVar u, leftVar pc == rightVar l, rightVar pc == leftVar r]
  colorConstraint i j pcs | (pc, (MF u r d)) = and [leftVar pc == bv (colorInt 'X') ColorBitSize,
                                                    upVar pc == downVar u, downVar pc == upVar d, rightVar pc == leftVar r]
  colorConstraint i j pcs | (pc, (ML u d l)) = and [rightVar pc == bv (colorInt 'X') ColorBitSize,
                                                    upVar pc == downVar u, downVar pc == upVar d, leftVar pc == rightVar l]
  colorConstraint i j pcs | (pc, (M u r d l)) = and [upVar pc == downVar u, downVar pc == upVar d,
                                                     leftVar pc == rightVar l, rightVar pc == leftVar r]

colorConstraints : Vect Dim (Vect Dim (PieceColors ColorBitSize)) -> Expr BoolT
colorConstraints pcs = and $ concat $ tabulate (\i => tabulate (\j => colorConstraint i j pcs))

pieceConstraint : Vect (Dim * Dim) (Int, Vect E Piece) -> Expr (BitVecT BitSize) -> PieceColors ColorBitSize -> Expr BoolT
pieceConstraint ps vp pc = or $ map (\(i, ps) => let ors = or $ map (\p => equalColors p pc) ps in 
                                                 bv i BitSize == vp && ors) ps

pieceConstraints : Vect (Dim * Dim) (Int, Vect E Piece) -> Vect Dim (Vect Dim (Expr (BitVecT BitSize))) -> Vect Dim (Vect Dim (PieceColors ColorBitSize)) -> Expr BoolT
pieceConstraints ps vps pcs = and $ concat $ tabulate (\i => tabulate (\j => pieceConstraint ps (index i j vps) (index i j pcs)))

solver : Smt ()
solver = do setLogic "QF_BV"
            setOption ":pp.bv-literals false"
            setOption ":model_validate true"
            varPieces <- declareVars varPieces (BitVecT BitSize)
            varColorPieces <- declareVars varColorPieces (BitVecT ColorBitSize)
            let varPieces = toVect varPieces
            let varColorPieces = toVect varColorPieces
            let colorPieces = mapColorPieces varColorPieces
            assert $ validPieces varPieces
            assert $ distinct $ concat varPieces
            assert $ colorConstraints colorPieces
            assert $ pieceConstraints pieces varPieces colorPieces
            checkSat
            getModel
            end

solution : Vect Dim (Vect Dim (Vect E String)) -> Model -> Vect Dim (Vect Dim String)
solution vcps model = tabulate (\i => tabulate (\j => let f = the (Fin E -> String)
                                                                  (\k => case lookup (index k $ index j $ index i vcps) model of
                                                                                  Nothing => ""
                                                                                  Just v => case parseInteger {a = Int} v of
                                                                                              Nothing => ""
                                                                                              Just x => cast $ intColor x) in
                                                      f 0 ++ f 1 ++ f 2 ++ f 3))

runSolver : IO ()
runSolver = do r <- sat solver
               case r of
                 Nothing => do putStrLn "Error parsing result"
                 Just (Sat, model) =>
                         putStrLn $ unlines $ toList $ map (unwords . toList) $ solution (toVect varColorPieces) model
                 Just (UnSat, _) => putStrLn "unsat"
                 Just (Unknown, _) => putStrLn "unknown"
