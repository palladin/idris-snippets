module Simplicity

-- Simplicity, based on https://blockstream.com/simplicity.pdf

data Ty = One | Sum Ty Ty | Prod Ty Ty

interpTy : Ty -> Type
interpTy One = Unit
interpTy (Sum x y) = Either (interpTy x) (interpTy y)
interpTy (Prod x y) = ((interpTy x), (interpTy y))

data Term : Ty -> Ty -> Type where
  Iden : Term a a
  Comp : Term a b -> Term b c -> Term a c
  Unit : Term a One
  InjL : Term a b -> Term a (Sum b c)
  InjR : Term a c -> Term a (Sum b c)
  Case : Term (Prod a c) d -> Term (Prod b c) d -> Term (Prod (Sum a b) c) d
  Pair : Term a b -> Term a c -> Term a (Prod b c)
  Take : Term a c -> Term (Prod a b) c
  Drop : Term b c -> Term (Prod a b) c

eval : Term a b -> interpTy a -> interpTy b
eval Iden = \a => a
eval (Comp x y) = \a => eval y (eval x a)
eval Unit = \_ => ()
eval (InjL x) = \a => Left (eval x a)
eval (InjR x) = \a => Right (eval x a)
eval (Case x y) = \(ab, c) => case ab of
                                Left l => eval x (l, c)
                                Right r => eval y (r, c)
eval (Pair x y) = \a => ((eval x a), (eval y a))
eval (Take x) = \(a, b) => eval x a
eval (Drop x) = \(a, b) => eval x b

Bit : Ty
Bit = Sum One One

not : Term Bit Bit
not = Comp (Pair Iden Unit) (Case (InjR Unit) (InjL Unit))

not' : interpTy Bit -> interpTy Bit
not' b = eval not b

zero : interpTy Bit
zero = Left ()

one : interpTy Bit
one = Right ()

test : interpTy Bit
test = not' zero
