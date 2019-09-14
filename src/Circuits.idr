module Circuits

interface Sym where
  Repr : Type

  lit : Bool -> Repr
  neg : Repr -> Repr
  (&&) : Repr -> Repr -> Repr
  (||) : Repr -> Repr -> Repr

[boolSym] Sym where
  Repr = Bool

  lit x = x
  neg x = not x
  (&&) x y = x && y
  (||) x y = x || y


[strSym] Sym where
  Repr = String

  lit x = if x then "tt" else "ff"
  neg x = "~" ++ x
  (&&) x y = "(" ++ x ++ " && " ++ y ++ ")"
  (||) x y = "(" ++ x ++ " || " ++ y ++ ")"

namespace Ex
  interface NAND where
    Repr : Type

    lit : Bool -> Repr
    nand : Repr -> Repr -> Repr

[strNAND] NAND where
  Repr = String

  lit x = if x then "tt" else "ff"
  nand x y =  "(" ++ x ++ " ^^ " ++ y ++ ")"

[nandSym] NAND => Sym where
  Repr = Ex.Repr

  lit x = Ex.lit x
  neg x = nand x x
  (&&) x y = neg (nand x y)
  (||) x y = nand (neg x) (neg y)

ex : Sym => Repr
ex = lit True && (neg (lit False))

test : String
test = ex @{nandSym @{strNAND}}
