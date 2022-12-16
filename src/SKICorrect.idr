module SKICorrect

-- Based on https://webspace.science.uu.nl/~swier004/publications/2021-jfp-submission-2.pdf

data U : Type where
  Base : U
  Arrow : U -> U -> U

Val : U -> Type
Val Base = Unit
Val (Arrow u1 u2) = Val u1 -> Val u2

Ctx : Type
Ctx = List U

data Ref' : U -> Ctx -> Type where
  Top : {Gamma : Ctx} -> Ref' t (t :: Gamma)
  Pop : {Gamma : Ctx} -> Ref' t Gamma -> Ref' t (t' :: Gamma)

data Term : Ctx -> U -> Type where
  App : {Gamma : Ctx} -> Term Gamma (Arrow a b) -> Term Gamma a -> Term Gamma b
  Lam : {Gamma : Ctx} -> Term (a :: Gamma) b -> Term Gamma (Arrow a b)
  Var : {Gamma : Ctx} -> Ref' t Gamma -> Term Gamma t

data Env : Ctx -> Type where
  Nil : Env []
  Cons : {Gamma : Ctx} -> Val t -> Env Gamma -> Env (t :: Gamma)

lookup : {Gamma : Ctx} -> Ref' t Gamma -> Env Gamma -> Val t
lookup Top (Cons x env) = x
lookup (Pop ref) (Cons x env) = lookup ref env

eval : {Gamma : Ctx} -> Term Gamma t -> Env Gamma -> Val t
eval (App t1 t2) env = (eval t1 env) (eval t2 env)
eval (Lam t) env = \x => eval t (Cons x env)
eval (Var x) env = lookup x env

data Comb : (Gamma : Ctx) -> (t : U) -> (Env Gamma -> Val t) -> Type where
  S : {Gamma : Ctx} -> Comb Gamma (Arrow (Arrow a (Arrow b c)) (Arrow (Arrow a b) (Arrow a c))) (\env => \f, g, x => (f x) (g x))
  K : {Gamma : Ctx} -> Comb Gamma (Arrow a (Arrow b a)) (\env => \x, y => x)
  I : {Gamma : Ctx} -> Comb Gamma (Arrow a a) (\env => \x => x)
  Var' : {Gamma : Ctx} -> (ref : Ref' t Gamma) -> Comb Gamma t (\env => lookup ref env)
  App' : {Gamma : Ctx} -> {f : Env Gamma -> Val (Arrow a b)} -> {x : Env Gamma -> Val a} ->
          Comb Gamma (Arrow a b) f -> Comb Gamma a x -> Comb Gamma b (\env => (f env) (x env))
