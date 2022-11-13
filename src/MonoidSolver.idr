module MonoidSolver

interface Monoid' a where
  neutral : a
  (<+>) : a -> a -> a
  neutralL : (x : a) -> neutral <+> x = x
  neutralR : (x : a) -> x <+> neutral = x
  assoc : (x : a) -> (y : a) -> (z : a) -> (x <+> (y <+> z)) = ((x <+> y) <+> z)

Monoid' (List a) where
  neutral = []
  (<+>) = (++)
  neutralL [] = Refl
  neutralL (x :: xs) = cong (neutralL xs)
  neutralR [] = Refl
  neutralR (x :: xs) = cong (neutralR xs)
  assoc [] ys zs = Refl
  assoc (x :: xs) ys zs = cong (assoc xs ys zs)

data MExpr : a -> Type where
  Add : MExpr a -> MExpr a -> MExpr a
  Zero : MExpr a
  Var : a -> MExpr a

eval : Monoid' a => MExpr a -> a
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

soundness : Monoid' a => (x : MExpr a) -> eval (normalise x) = eval x
soundness (Add e1 e2) = ?dsdfsf_1
soundness Zero = Refl
soundness (Var x) = neutralR x

solve : Monoid' a => (x : MExpr a) -> (y : MExpr a) -> eval (normalise x) = eval (normalise y) -> eval x = eval y
solve (Add e1 e2) (Add e1' e2') prf = ?fsdf
solve (Add e1 e2) (Var y) prf = ?sfdfs
solve x Zero prf = rewrite sym prf in sym (soundness x)
solve Zero y prf = rewrite prf in soundness y
solve (Var x) y prf with (replace {P = (\x => x = eval (normalise y))} (neutralR x) prf)
  solve (Var x) y prf | prf' = rewrite prf' in soundness y


example : (xs : List a) -> (ys : List a) -> (zs : List a) -> ((xs ++ []) ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
example [] ys zs = Refl
example (x :: xs) ys zs = cong {f = (\xs => x :: xs)} (example xs ys zs)

example' : (xs : List a) -> (ys : List a) -> (zs : List a) -> ((xs ++ []) ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
example' xs ys zs =
  let e1 = Add (Add (Var xs) Zero) (Add (Var ys) (Var zs)) in
  let e2 = Add (Add (Var xs) (Var ys)) (Var zs) in
  solve e1 e2 Refl
