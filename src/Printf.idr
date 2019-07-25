module Printf

-- Based on https://strathprints.strath.ac.uk/68800/

import Data.Vect
import src.GenericArity

data Chunk : Type where
  IntC : Chunk
  RawC : Char -> Chunk

Format : Type
Format = List Chunk

size' : Format -> Nat
size' [] = 0
size' (IntC :: xs) = 1 + size' xs
size' ((RawC x) :: xs) = size' xs

parse : List Char -> Format
parse [] = []
parse ('%' :: 'd' :: xs) = IntC :: parse xs
parse (x :: xs) = RawC x :: parse xs

format : (fmt : Format) -> Types (size' fmt)
format [] = []
format (IntC :: fmt) = Int :: format fmt
format ((RawC _) :: fmt) = format fmt

assemble : (fmt : Format) -> Product (size' fmt) (format fmt) -> List String
assemble [] () = []
assemble (IntC :: fmt) (n, vs) = show n :: assemble fmt vs
assemble ((RawC c) :: fmt) vs = pack (the (List Char) [c])  :: assemble fmt vs

printf : (str : String) -> Arrows (size' (parse (unpack str))) (format (parse (unpack str))) String
printf str = let fmt = parse (unpack str) in curryn (size' (parse (unpack str))) (concat . assemble (parse (unpack str)))

lessThan : Int -> Int -> String
lessThan = printf "%d < %d"
