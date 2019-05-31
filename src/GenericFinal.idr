module GenericFinal


interface Symantics (rep : Type -> Type) where
  int : rep Int
  bool : rep Bool
  tuple : rep a -> rep b -> rep (a, b)
  list : rep a -> rep (List a)
  maybe : rep a -> rep (Maybe a)

data Printer : Type -> Type where
  P : (a -> String) -> Printer a

Symantics Printer where
  int = P (\x => show x)
  bool = P (\x => show x)
  tuple (P f) (P g) = P (\(x, y) => "(" ++ (f x) ++ ", " ++ (g y) ++ ")")
  list (P f) = P (\xs => let res = foldr (\elem, acc => if acc == "" then f elem else (f elem) ++ ", " ++ acc) "" xs in "[" ++ res ++ "]")
  maybe (P f) = P p
    where
      p : Maybe a -> String
      p Nothing = "Nothing"
      p (Just x) = "Just " ++ f x

print : Printer a -> a -> String
print (P f) = f

example : (List Int, Maybe Bool) -> String
example = print (tuple (list int) (maybe bool))
