module SMTLib

data TypeT : Type where
  BoolT : TypeT
  BitVecT : Nat -> TypeT

Show TypeT where
  show BoolT = "Bool"
  show (BitVecT n) = "BitVec " ++ show n

interface Symantics (rep : TypeT -> Type) where
  bool : Bool -> rep BoolT
  int : Int -> (n : Nat) -> rep (BitVecT n)
  bitVar : String -> (n : Nat) -> rep (BitVecT n)
  (+) : rep (BitVecT n) -> rep (BitVecT n) -> rep (BitVecT n)
  (*) : rep (BitVecT n) -> rep (BitVecT n) -> rep (BitVecT n)
  (==) : rep a -> rep a -> rep BoolT
  (&&) : rep BoolT -> rep BoolT -> rep BoolT
  (||) : rep BoolT -> rep BoolT -> rep BoolT
  not : rep BoolT -> rep BoolT
  ite : rep BoolT -> rep BoolT -> rep BoolT -> rep BoolT


data Code : TypeT -> Type where
  C : Int -> List (String, TypeT) -> String -> Code a

Symantics Code where
