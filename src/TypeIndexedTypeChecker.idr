module TypeIndexedTypeChecker

-- Based on https://cs.brynmawr.edu/~rae/papers/2018/stitch/stitch.pdf

import Data.Fin
import Data.List
import Data.Vect
import Control.Catchable

data Ty : Type where
  TyInt : Ty
  TyFun : Ty -> Ty -> Ty

-- lemmas
notIntFun : TyInt = TyFun x y -> Void
notIntFun Refl impossible
notFunInt : (TyFun x y) = TyInt -> Void
notFunInt Refl impossible
xEqyNeq : (x = x') -> ((y = y') -> Void) -> TyFun x y = TyFun x' y' -> Void
xEqyNeq Refl contra Refl = contra Refl
xNeqyEq : (y = y') -> ((x = x') -> Void) -> TyFun x y = TyFun x' y' -> Void
xNeqyEq Refl contra Refl = contra Refl
xNeqyNEq : ((x = x') -> Void) -> ((y = y') -> Void) -> TyFun x y = TyFun x' y' -> Void
xNeqyNEq contra contra' Refl = contra Refl

implementation DecEq Ty where
  decEq TyInt TyInt = Yes Refl
  decEq TyInt (TyFun x y) = No notIntFun
  decEq (TyFun x y) TyInt = No notFunInt
  decEq (TyFun x y) (TyFun x' y') with (decEq x x')
    decEq (TyFun x'' y) (TyFun x'' y') | (Yes Refl) with (decEq y y')
      decEq (TyFun x'' y'') (TyFun x'' y'') | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (TyFun x'' y) (TyFun x'' y') | (Yes Refl) | (No contra) = No (\eq => xEqyNeq Refl contra eq)
    decEq (TyFun x y) (TyFun x' y') | (No contra) with (decEq y y')
      decEq (TyFun x y'') (TyFun x' y'') | (No contra) | (Yes Refl) = No (\eq => xNeqyEq Refl contra eq)
      decEq (TyFun x y) (TyFun x' y') | (No contra) | (No contra') = No (\eq => xNeqyNEq contra contra' eq)

data UExp : Nat -> Type where
  UVar : Fin n -> UExp n
  ULam : Ty -> UExp (S n) -> UExp n
  UApp : UExp n -> UExp n -> UExp n
  UPlus : UExp n -> UExp n -> UExp n
  UIntE : Int -> UExp n


data Expr : Vect n Ty -> Ty -> Type where
  Val : Int -> Expr ctx TyInt
  Plus : Expr ctx TyInt -> Expr ctx TyInt -> Expr ctx TyInt
  Var : Elem t ctx -> Expr ctx t
  Lam : Expr (a :: ctx) b -> Expr ctx (TyFun a b)
  App : Expr ctx (TyFun a b) -> Expr ctx a -> Expr ctx b


interpTy : Ty -> Type
interpTy TyInt = Int
interpTy (TyFun arg res) = interpTy arg -> interpTy res

interpCtx : Vect n Ty -> Type
interpCtx [] = ()
interpCtx (t :: ts) = (interpTy t, interpCtx ts)

lookup : Elem t ctx -> interpCtx ctx -> interpTy t
lookup Here (t, _) = t
lookup (There x) (_, ts) = lookup x ts

show : (t : Ty) -> interpTy t -> String
show TyInt v = show v
show (TyFun x y) v = "Fun"

eval : interpCtx ctx -> Expr ctx t -> interpTy t
eval ctx (Val x) = x
eval ctx (Var x) = lookup x ctx
eval ctx (Lam body) = \x => eval (x, ctx) body
eval ctx (App f x) = (eval ctx f) (eval ctx x)
eval ctx (Plus e1 e2) = (eval ctx e1) + (eval ctx e2)

check : (Catchable m String) => UExp Z -> ((t : Ty) -> Expr [] t -> m r) -> m r
check uexp k = go [] uexp k
  where
    go : (Catchable m String) => (ctx : Vect n Ty) -> UExp n -> ((t : Ty) -> Expr ctx t -> m r) -> m r
    go ctx (UVar n) k = checkVar n ctx $ \ty, elem => k ty (Var elem)
      where
        checkVar : (Catchable m String) => {n : Nat} -> Fin n -> (ctx : Vect n Ty) -> ((t : Ty) -> Elem t ctx -> m r) -> m r
        checkVar FZ (ty :: _) k = k ty Here
        checkVar (FS n') (_ :: ctx') k = checkVar n' ctx' $ \ty, elem => k ty (There elem)

    go ctx (ULam ty body) k = go (ty :: ctx) body $ \resTy, body' => k (TyFun ty resTy) (Lam body')
    go ctx (UApp e1 e2) k = go ctx e1 $ \funTy, e1' =>
                            go ctx e2 $ \argTy, e2' => checkApp funTy argTy e1' e2' k
      where
        checkApp : (Catchable m String) => (funTy : Ty) -> (argTy : Ty) -> Expr ctx funTy -> Expr ctx argTy -> ((t : Ty) -> Expr ctx t -> m r) -> m r
        checkApp (TyFun argTy' resTy) argTy e1' e2' k with (decEq argTy' argTy)
          checkApp (TyFun argTy resTy) argTy e1' e2' k | (Yes Refl) = k resTy (App e1' e2')
          checkApp (TyFun argTy' refTy) argTy e1' e2' k | (No contra) = throw "TypeError"
        checkApp _ _ e1' e2' k = throw "TypeError"
    go ctx (UPlus e1 e2) k = go ctx e1 $ \ty1, e1' =>
                             go ctx e2 $ \ty2, e2' => checkPlus ty1 ty2 e1' e2' k
      where
        checkPlus : (Catchable m String) => (ty1 : Ty) -> (ty2 : Ty) -> Expr ctx ty1 -> Expr ctx ty2 -> ((t : Ty) -> Expr ctx t -> m r) -> m r
        checkPlus TyInt TyInt e1' e2' k = k TyInt (Plus e1' e2')
        checkPlus _ _ e1' e2' k = throw "TypeError"
    go ctx (UIntE x) k = k TyInt (Val x)


example : UExp Z
example = UApp (ULam TyInt (UPlus (UVar FZ) (UIntE 1))) (UIntE 5)

test : Either String String
test = check example (\ty, expr => Right $ show ty $ eval () expr)
