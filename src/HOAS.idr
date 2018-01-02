module HOAS



data Expr : Type -> Type where
  Val : a -> Expr a
  Op : (a -> b -> c) -> Expr a -> Expr b -> Expr c
  If : Expr Bool -> Expr a -> Expr a -> Expr a
  Lam : (Expr a -> Expr b) -> Expr (a -> b)
  App : Expr (a -> b) -> Expr a -> Expr b
  Fix : Expr ((a -> b) -> (a -> b)) -> Expr (a -> b)


eval : Expr a -> a
eval (Val x) = x
eval (Op f x y) = f (eval x) (eval y)
eval (If p x y) = if (eval p) then (eval x) else (eval y)
eval (Lam f) = \x => eval (f (Val x))
eval (App f x) = (eval f) (eval x)
eval (Fix f) = \x => loop f x
  where
    loop : Expr ((a -> b) -> (a -> b)) -> a -> b
    loop f a = (eval f) (loop f) a


example : Expr (Int -> Int)
example = Fix (Lam (\f => (Lam (\x =>
                    If (Op (==) x (Val 0))
                      (Val 1)
                      (Op (*) x (App f (Op (-) x (Val 1))))))))

test : Int
test = eval example 5
