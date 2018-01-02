module STLCInterp

data HasType : List a -> a -> Type where
  VZ : HasType (t :: env) t
  VS : HasType env t -> HasType (_ :: env) t

data Expr : List Type -> Type -> Type where
  Val : Int -> Expr env Int
  Var : HasType env t -> Expr env t
  Lam : Expr (a :: env) b -> Expr env (a -> b)
  App : Expr env (a -> b) -> Expr env a -> Expr env b


interpEnv : List Type -> Type
interpEnv [] = ()
interpEnv (x :: xs) = (x, interpEnv xs)

lookup : HasType env t -> interpEnv env -> t
lookup VZ (t, _) = t
lookup (VS x) (_, ts) = lookup x ts

eval : interpEnv env -> %static Expr env t -> t
eval env (Val x) = x
eval env (Var x) = lookup x env
eval env (Lam body) = \x => eval (x, env) body
eval env (App f x) = (eval env f) (eval env x)

example : Expr [] Int
example = App (Lam (Var VZ)) (Val 42)

test : Int
test = eval () example
