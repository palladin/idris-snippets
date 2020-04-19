module Eternity2SMT

import Data.Vect
import src.SMTLib
import src.Tensor

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
