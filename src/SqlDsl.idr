module SqlDsl

import Data.Vect

--%access public export

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
  Field : {t : SqlType} -> (alias : String) -> (name : String) -> SqlExpr t


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

get : (t : (String, SqlType)) -> {ts : Vect n (String, SqlType)} -> Tuple (\t => SqlExpr (snd t)) ts -> {auto p : Elem t ts} -> SqlExpr (snd t)
get t (x :: xs) {p = Here} = x
get t (x :: xs) {p = There p'} = get t {p = p'} xs

data SqlQuery : Vect n (String, SqlType) -> Type where
  From : (t : Table) -> SqlQuery (snd t)
  Product : SqlQuery ts -> SqlQuery ts' -> (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts' -> Tuple (\t => SqlExpr (snd t)) ts'') -> SqlQuery ts''
  Where : SqlQuery ts -> (Tuple (\t => SqlExpr (snd t)) ts -> SqlExpr SqlBool) -> SqlQuery ts
  Select : SqlQuery ts -> (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts') -> SqlQuery ts'

from : (t : Table) -> SqlQuery (snd t)
from t = From t

product : (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts' -> Tuple (\t => SqlExpr (snd t)) ts'') -> SqlQuery ts -> SqlQuery ts' -> SqlQuery ts''
product proj q1 q2 = Product q1 q2 proj

where' : (Tuple (\t => SqlExpr (snd t)) ts -> SqlExpr SqlBool) -> SqlQuery ts -> SqlQuery ts
where' pred query = Where query pred

select : (Tuple (\t => SqlExpr (snd t)) ts -> Tuple (\t => SqlExpr (snd t)) ts') -> SqlQuery ts -> SqlQuery ts'
select f query = Select query f

compileExpr : SqlExpr t -> String
compileExpr (IntC x) = show x
compileExpr (BoolC x) = show x
compileExpr (StringC x) = "\"" ++ x ++ "\""
compileExpr (PlusC x y) = "(" ++ compileExpr x ++ " + " ++ compileExpr y ++ ")"
compileExpr (ConcatC x y) = "(" ++ compileExpr x ++ " ++ " ++ compileExpr y ++ ")"
compileExpr (EqualC x y) = "(" ++ compileExpr x ++ " = " ++ compileExpr y ++ ")"
compileExpr (NotC x) = "NOT" ++ compileExpr x
compileExpr (Field alias name) = alias ++ "." ++ name

mapToTuple : String -> (ts : Vect n (String, SqlType)) -> Tuple (\t => SqlExpr (snd t)) ts
mapToTuple alias [] = []
mapToTuple alias ((name, t) :: ts) = Field {t = t} alias name :: mapToTuple alias ts

tupleToString : {ts : Vect n (String, SqlType)} -> Tuple (\t => SqlExpr (snd t)) ts -> String
tupleToString {ts = []} [] = ""
tupleToString {ts = [t]} [e] = compileExpr e ++ " AS " ++ fst t
tupleToString {ts = t :: ts} (e :: es) = compileExpr e ++ " AS " ++ fst t ++ ", " ++ tupleToString es

compile' : {ts : Vect n (String, SqlType)} -> SqlQuery ts -> Int -> (Int -> String -> String) -> String
compile' (Select {ts} (From (tableName, _)) f) i k =
  let alias = "c" ++ show i in
  let tuple' = f $ mapToTuple alias ts in
  let sql = "SELECT " ++ tupleToString tuple' ++ " FROM " ++ tableName ++ " AS " ++ alias in
  k (i + 1) sql
compile' (Select {ts} (Where (From (tableName, _)) pred) f) i k =
  let alias = "c" ++ show i in
  let tuple' = f $ mapToTuple alias ts in
  let sql = "SELECT " ++ tupleToString tuple' ++ " FROM " ++ tableName ++ " AS " ++ alias ++ " WHERE " ++ (compileExpr $ pred $ mapToTuple alias ts) in
  k (i + 1) sql
compile' (From (tableName, ts)) i k =
  let alias = "c" ++ show i in
  let sql = "SELECT * FROM " ++ tableName ++ " AS " ++ alias in
  k (i + 1) sql
compile' {ts} (Where query pred) i k =
  compile' query i (\i, sql =>
    let alias = "c" ++ show i in
    let sql' = "SELECT * FROM (" ++ sql ++ ") AS " ++ alias ++ " WHERE " ++ (compileExpr $ pred $ mapToTuple alias ts) in
    k (i + 1) sql')
compile' (Select {ts} query f) i k =
  compile' query i (\i, sql =>
    let alias = "c" ++ show i in
    let tuple' = f $ mapToTuple alias ts in
    let sql' = "SELECT " ++ tupleToString tuple' ++ " FROM (" ++ sql ++ ") AS " ++ alias in
    k (i + 1) sql')
compile' (Product {ts} {ts'} q1 q2 f) i k =
  compile' q1 i (\i, sql =>
    compile' q2 i (\i, sql' =>
      let alias = "c" ++ show i in
      let i' = i + 1 in
      let alias' = "c" ++ show i' in
      let tuple' = f (mapToTuple alias ts) (mapToTuple alias' ts') in
      let sql'' = "SELECT " ++ tupleToString tuple' ++ " FROM (" ++ sql ++ ") AS " ++ alias ++ ", (" ++ sql' ++ ") AS " ++ alias' in
      k (i' + 1) sql''))

compile : SqlQuery ts -> String
compile query = compile' query 0 (\_, sql => sql)


customer : Table {n = 3}
customer = ("Customer", [("Id", SqlInt),
                         ("Name", SqlString),
                         ("Age", SqlInt)])

--
example0 : SqlQuery [("Id", SqlInt), ("Name", SqlString), ("Age", SqlInt)]
example0 = from customer

example1 : SqlQuery [("Name", SqlString)]
example1 = select (\ta  => [get ("Name", SqlString) {ts = snd customer} ta]) $ from customer

example2 : SqlQuery [("Id", SqlInt)]
example2 = select (\ta => [index 0 ta]) $ from customer

example3 : SqlQuery [("Id", SqlInt), ("Age", SqlInt)]
example3 = select (\ta => [index 0 ta, index 2 ta]) $ where' (\ta => index 1 ta == str "Nick") $ from customer
