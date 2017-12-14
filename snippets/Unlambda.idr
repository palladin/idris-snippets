module Unlambda

-- Based on http://www.madore.org/~david/programs/unlambda/

data Cont : (m : Type -> Type) -> (r : Type) -> Type where
   Cont' : ((Cont m r, (Cont m r -> m r)) -> m r) -> Cont m r

data Expr : Type where
  S : Expr
  K : Expr
  I : Expr
  R : Expr
  C : Expr
  Dot : Char -> Expr
  Backtick : Expr -> Expr -> Expr

apply : ((Cont m r -> m r) -> m r) -> ((Cont m r -> m r) -> m r) -> (Cont m r -> m r) -> m r
apply first second = \k => first (\(Cont' c) => second (\c' => c (c', k)))
unit : Cont m r -> (Cont m r -> m r) -> m r
unit c = \k => k c

eval : Monad m => Expr -> (Char -> m ()) -> (Cont m r -> m r) -> m r
eval S put = \k => k (Cont' (\(c, k') =>
                   k' (Cont' (\(c', k'') =>
                   k'' (Cont' (\(c'', k''') => (apply (apply (unit c) (unit c'')) (apply (unit c') (unit c''))) k'''))))))
eval K put = \k => k (Cont' (\(c, k') => k' (Cont' (\(_, k'') => k'' c))))
eval I put = \k => k (Cont' (\(c, k') => k' c))
eval R put = \k => k (Cont' (\(c, k') => do put '\n'; k' c))
eval C put = \k => k (Cont' (\(Cont' c, k') => c (Cont' (\(c', _) => k' c'), k')))
eval (Dot char) put = \k => k (Cont' (\(c, k') => do put char; k' c))
eval (Backtick expr expr') put = apply (eval expr put) (eval expr' put)


parse :  List Char -> Maybe (Expr, List Char)
parse ('s' :: xs) = Just (S, xs)
parse ('k' :: xs) = Just (K, xs)
parse ('i' :: xs) = Just (I, xs)
parse ('r' :: xs) = Just (R, xs)
parse ('c' :: xs) = Just (C, xs)
parse ('.' :: c :: xs) = Just (Dot c, xs)
parse ('`' :: xs) = do (expr, xs') <- parse xs
                       (expr', xs'') <- parse xs'
                       Just (Backtick expr expr', xs'')
parse (x :: xs) = Nothing
parse [] = Nothing

test : String
test = "```si`k``s.H``s.e``s.l``s.l``s.o``s. ``s.w``s.o``s.r``s.l``s.d``s.!``sri``si``si``si``si``si``si``si``si`ki"

example : IO ()
example = case parse (unpack test) of
            Just (expr, _) => eval expr putChar (\_ => pure ())
            Nothing => putStrLn "Parse error"
