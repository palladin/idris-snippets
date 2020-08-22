module SqlDsl

import Control.Pipeline
import Data.Vect

data SqlType : Type where
  SqlInt : SqlType
  SqlBool : SqlType
  SqlString : SqlType

data SqlExpr : SqlType -> Type where
  IntC : Int -> SqlExpr SqlInt
  BoolC : Bool -> SqlExpr SqlBool
  StringC : String -> SqlExpr SqlString
  PlusC : SqlExpr SqlInt -> SqlExpr SqlInt -> SqlExpr SqlInt
  ConcatC : SqlExpr SqlString -> SqlExpr SqlString -> SqlExpr SqlString
  EqualC : SqlExpr a -> SqlExpr a -> SqlExpr SqlBool
  NotC : SqlExpr SqlBool -> SqlExpr SqlBool


int : Int -> SqlExpr SqlInt
int x = IntC x

bool : Bool -> SqlExpr SqlBool
bool x = BoolC x

str : String -> SqlExpr SqlString
str x = StringC x

(==) : SqlExpr a -> SqlExpr a -> SqlExpr SqlBool
(==) x y = EqualC x y

data Tuple : {a : Type} -> (f : a -> Type) -> Vect n a -> Type where
  Nil : Tuple f []
  (::) : f t -> Tuple f ts -> Tuple f (t :: ts)

Table : {n : Nat} -> Type
Table {n} = (String, Vect n (String, SqlType))

index : (i : Fin k) -> Tuple f ts -> f (index i ts)
index FZ (x::xs) = x
index (FS j) (x::xs) = index j xs

get : {t : (String, SqlType)} -> {ts : Vect n (String, SqlType)} -> Tuple (\t => SqlExpr (snd t)) ts -> {auto p : Elem t ts} -> SqlExpr (snd t)
get (x :: xs) {p = Here} = x
get (x :: xs) {p = There p'} = get {p = p'} xs

data SqlQuery : Vect n (String, SqlType) -> Type where
  From : (t : Table) -> SqlQuery (snd t)
  Where : SqlQuery ts -> (Tuple (\t => SqlExpr (snd t)) ts -> SqlExpr SqlBool) -> SqlQuery ts
  Select : SqlQuery ts -> (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts') -> SqlQuery ts'

from : (t : Table) -> SqlQuery (snd t)
from t = From t

where' : (Tuple (\t => SqlExpr (snd t)) ts -> SqlExpr SqlBool) -> SqlQuery ts -> SqlQuery ts
where' pred query = Where query pred

select : (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts') -> SqlQuery ts -> SqlQuery ts'
select f query = Select query f


customer : Table {n = 3}
customer = ("Customer", [("Id", SqlInt),
                         ("Name", SqlString),
                         ("Age", SqlInt)])

--
example : SqlQuery [("Id", SqlInt), ("Name", SqlString), ("Age", SqlInt)]
example = from customer

example1 : SqlQuery [("Name", SqlString)]
example1 = select (\ta => [get {t = ("Name", SqlString)} {ts = snd customer} ta]) $ from customer

example2 : SqlQuery [("Id", SqlInt)]
example2 = select (\ta => [index 0 ta]) $ from customer

example3 : SqlQuery [("Id", SqlInt)]
example3 = select (\ta => [index 0 ta]) $ where' (\ta => index 1 ta == str "Nick") $ from customer
