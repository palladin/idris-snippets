module TypedNBE

-- Typed NBE, based on https://hal.inria.fr/hal-01397929/document

import Data.Vect

data Ty = Base String | Arrow Ty Ty

data Syn : Vect n Ty -> Ty -> Type where
  Var : Elem a ctx -> Syn ctx a
  Lam : Syn (a :: ctx) b -> Syn ctx (Arrow a b)
  App : Syn ctx (Arrow a b) -> Syn ctx a -> Syn ctx b

V : Ty -> Type

mutual
  data Nf : Ty -> Type where
    NLam : (V a -> Nf b) -> Nf (Arrow a b)
    NAt : At (Base a) -> Nf (Base a)

  data At : Ty -> Type where
    AApp : At (Arrow a b) -> Nf a -> At b
    AVar : V a -> At a

data Sem : Ty -> Type where
  Fun : (Sem a -> Sem b) -> Sem (Arrow a b)
  Base' : At (Base a) -> Sem (Base a)

data Env : Vect n Ty -> Type where
  Nil  : Env Nil
  (::) : Sem ty -> Env ctx -> Env (ty :: ctx)

lookup' : Elem ty ctx -> Env ctx -> Sem ty
lookup' Here (x :: _) = x
lookup' (There later) (x :: xs) = lookup' later xs

eval : Env ctx -> Syn ctx ty -> Sem ty
eval env (Var x) = lookup' x env
eval env (Lam body) = Fun (\x => eval (x :: env) body)
eval env (App f x) with (eval env f)
  eval env (App f x) | (Fun f') = f' (eval env x)

mutual
  reflect : At ty -> Sem ty
  reflect {ty = (Base _)} at = Base' at
  reflect {ty = (Arrow a b)} at = Fun (\x => reflect (AApp at (reify x)))

  reify : Sem ty -> Nf ty
  reify {ty = (Base _)} (Base' base) = NAt base
  reify {ty = (Arrow a b)} (Fun f) = NLam (\x => reify (f (reflect (AVar x))))

nbe : Syn [] ty -> Nf ty
nbe syn = reify (eval [] syn)

example : Syn [] (Arrow (Base "a") (Base "a"))
example = Lam (App (Lam (Var Here)) (Var Here))

test : Nf (Arrow (Base "a") (Base "a"))
test = nbe example
