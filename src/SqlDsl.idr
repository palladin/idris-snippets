module SqlDsl

import Data.Vect
import Control.Pipeline

data SqlType : Type where
  SqlInt : SqlType
  SqlBool : SqlType
  SqlString : SqlType

data SqlExpr : SqlType -> Type where
  IntC : Int -> SqlExpr SqlInt
  BoolC : Bool -> SqlExpr SqlInt
  StringC : String -> SqlExpr SqlString
  PlusC : SqlExpr SqlInt -> SqlExpr SqlInt -> SqlExpr SqlInt
  ConcatC : SqlExpr SqlString -> SqlExpr SqlString -> SqlExpr SqlString
  EqualC : SqlExpr a -> SqlExpr a -> SqlExpr SqlBool
  NotC : SqlExpr SqlBool -> SqlExpr SqlBool

data Tuple : Vect n SqlType -> Type where
  Nil : Tuple []
  (::) : SqlExpr t -> Tuple ts -> Tuple (t :: ts)
