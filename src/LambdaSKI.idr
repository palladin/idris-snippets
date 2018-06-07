module LambdaSKI

-- Based on http://okmij.org/ftp/tagless-final/ski.pdf

data HasType : List a -> a -> Type where
  VZ : HasType (t :: env) t
  VS : HasType env t -> HasType (_ :: env) t

data Expr : List Type -> Type -> Type where
  Var : HasType env t -> Expr env t
  Lam : Expr (a :: env) b -> Expr env (a -> b)
  App : Expr env (a -> b) -> Expr env a -> Expr env b

data SKI : Type -> Type where
  KI : SKI (a -> a)
  KK : SKI (a -> b -> a)
  KS : SKI ((a -> b -> c) -> (a -> b) -> a -> c)
  KB : SKI ((a -> b) -> (c -> a) -> c -> b)
  KC : SKI ((a -> b -> c) -> b -> a -> c)
  KApp : SKI (a -> b) -> SKI a -> SKI b

data Repr : List Type -> Type -> Type where
  C : SKI a -> Repr env a
  N : Repr env (a -> b) -> Repr (a :: env) b
  W : Repr env a -> Repr (_ :: env) a

app : Repr env (a -> b) -> Repr env a -> Repr env b
app (C x) (C y) = C $ KApp x y
app (C x) (N y) = N $ app (C (KApp KB x)) y
app (C x) (W y) = W $ app (C x) y
app (N x) (C y) = N $ app (C  (KApp (KApp KC KC) y)) x
app (N x) (N y) = N $ app (app (C KS) x) y
app (N x) (W y) = N $ app (app (C KC) x) y
app (W x) (C y) = W $ app x (C y)
app (W x) (N y) = N $ app (app (C KB) x) y
app (W x) (W y) = W $ app x y

conv : Expr env a -> Repr env a
conv (Var VZ) = N $ C KI
conv (Var (VS x)) = W $ conv (Var x)
conv (Lam x) with (conv x)
  conv (Lam x) | (C y) = C $ KApp KK y
  conv (Lam x) | (N y) = y
  conv (Lam x) | (W y) = app (C KK) y
conv (App f x) = app (conv f) (conv x)

comp : Expr [] a -> SKI a
comp expr with (conv expr)
  comp expr | (C x) = x

example : Expr [] ((() -> ()) -> () -> ())
example = Lam (Lam (App (Var (VS VZ)) (Var VZ)))

test : SKI ((() -> ()) -> () -> ())
test = comp example
