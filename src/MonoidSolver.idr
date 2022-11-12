module MonoidSolver

data MExpr : a -> Type where
  Add : MExpr a -> MExpr a -> MExpr a
  Zero : MExpr a
  Var : a -> MExpr a

eval : Monoid a => MExpr a -> a
eval (Add e1 e2) = eval e1 <+> eval e2
eval Zero = neutral
eval (Var x) = x

translate : MExpr a -> (MExpr a -> MExpr a)
translate (Add e1 e2) = \y => (translate e1) (translate e2 y)
translate Zero = \y => y
translate (Var x) = \y => Add (Var x) y

reify : (MExpr a -> MExpr a) -> MExpr a
reify f = f Zero

normalise : MExpr a -> MExpr a
normalise m = reify (translate m)

example : (xs : List a) -> (ys : List a) -> (zs : List a) -> ((xs ++ []) ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
example [] ys zs = Refl
example (x :: xs) ys zs = cong {f = (\xs => x :: xs)} (example xs ys zs)
