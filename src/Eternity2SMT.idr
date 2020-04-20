module Eternity2SMT

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

colorConstraint : Fin Dim -> Fin Dim -> Vect Dim (Vect Dim (PieceColors ColorBitSize)) -> Expr BoolT
colorConstraint i j pcs with (toPos i, toPos j)
  colorConstraint i j pcs | (First, First) = ?fooo1
  colorConstraint i j pcs | (Last, Last) = ?fooo2
  colorConstraint i j pcs | (First, Last) = ?fooo3
  colorConstraint i j pcs | (Last, First) = ?fooo4
  colorConstraint i j pcs | (First, _) = ?fooo5
  colorConstraint i j pcs | (Last, _) = ?fooo6
  colorConstraint i j pcs | (_, First) = ?fooo7
  colorConstraint i j pcs | (_, Last) = ?fooo8
  colorConstraint i j pcs | (_, _) = ?fooo9


solver : Smt ()
solver = do varPieces <- declareVars varPieces (BitVecT BitSize)
            varColorPieces <- declareVars varColorPieces (BitVecT ColorBitSize)
            let varPieces = toVect varPieces
            let varColorPieces = toVect varColorPieces
            let colorPieces = mapColorPieces varColorPieces
            assert $ validPieces varPieces
            ?foo
            end
