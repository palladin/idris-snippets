module MonoidSolver

-- Based on https://www.cambridge.org/core/journals/journal-of-functional-programming/article/wellknown-representation-of-monoids-and-its-application-to-the-function-vector-reverse/929D15452762F6BB0A4A68503026D1C4

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


lemma2 : Monoid' a => (x : MExpr a) -> (y : MExpr a) -> eval (translate x y) = eval (Add x y)
lemma2 (Add x y) z =
  rewrite sym (assoc (eval x) (eval y) (eval z)) in
  rewrite sym (lemma2 y z) in
  lemma2 x (translate y z)
lemma2 Zero y = rewrite neutralL (eval y) in Refl
lemma2 (Var x) y = Refl

lemma1 : Monoid' a => (x : MExpr a) -> (y : MExpr a) -> eval (normalise (Add x y)) = eval (translate x y)
lemma1 (Add x y) z =
  rewrite lemma2 x (translate y z) in
  rewrite sym (lemma1 y z) in
  lemma2 x (translate y (translate z Zero))
lemma1 (Var x) (Add y z) = rewrite sym (lemma2 y z) in rewrite lemma1 y z in Refl
lemma1 (Var x) Zero = Refl
lemma1 (Var x) (Var y) = rewrite neutralR y in Refl
lemma1 Zero (Add x y) = rewrite sym (lemma2 x y) in rewrite lemma1 x y in Refl
lemma1 Zero Zero = Refl
lemma1 Zero (Var x) = neutralR x

soundness : Monoid' a => (x : MExpr a) -> eval (normalise x) = eval x
soundness (Add e1 e2) = rewrite sym (lemma2 e1 e2) in rewrite lemma1 e1 e2 in Refl
soundness Zero = Refl
soundness (Var x) = neutralR x

solve : Monoid' a => (x : MExpr a) -> (y : MExpr a) -> eval (normalise x) = eval (normalise y) -> eval x = eval y
solve (Add e1 e2) (Add e1' e2') prf =
  rewrite sym (lemma2 e1 e2) in
  rewrite sym (lemma2 e1' e2') in
  rewrite sym (lemma1 e1 e2) in
  rewrite sym (lemma1 e1' e2') in
  prf
solve (Add e1 e2) (Var y) prf =
  rewrite sym (neutralR y) in
  rewrite sym prf in
  rewrite sym (lemma2 e1 e2) in
  rewrite lemma1 e1 e2 in Refl
solve x Zero prf = rewrite sym prf in sym (soundness x)
solve Zero y prf = rewrite prf in soundness y
solve (Var x) y prf = rewrite sym (neutralR x) in rewrite prf in soundness y


example : (xs : List a) -> (ys : List a) -> (zs : List a) -> ((xs ++ []) ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
example [] ys zs = Refl
example (x :: xs) ys zs = cong {f = (\xs => x :: xs)} (example xs ys zs)

example' : (xs : List a) -> (ys : List a) -> (zs : List a) -> ((xs ++ []) ++ (ys ++ zs)) = ((xs ++ ys) ++ zs)
example' xs ys zs =
  let e1 = Add (Add (Var xs) Zero) (Add (Var ys) (Var zs)) in
  let e2 = Add (Add (Var xs) (Var ys)) (Var zs) in
  solve e1 e2 Refl
