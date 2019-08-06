module Diff

-- Based on https://arxiv.org/pdf/1803.10228.pdf

import src.Expr


interface DiffSymantics (rep : TypeT -> Type) where
  d : Double -> rep DoubleT
  (+) : rep DoubleT -> rep DoubleT -> rep DoubleT
  (*) : rep DoubleT -> rep DoubleT -> rep DoubleT
  grad : (rep DoubleT -> rep DoubleT) -> Code (ArrowT DoubleT DoubleT)


data Reverse : TypeT -> Type where
  R : (((Code DoubleT, Code (VarT DoubleT)) -> Code UnitT) -> Code UnitT) -> Reverse a


DiffSymantics Reverse where
  d x = R (\k => letVal (double x) (\x => newVar (double 0) (\d => k (x, d))))

  (+) (R l) (R r) = R (\k => l (\(lv, ld) =>
                             r (\(rv, rd) => letVal (lv <+> rv) (\x =>
                                             newVar (double 0) (\d =>
                                                  seqs [k (x, d),
                                                  assign (deref ld <+> deref d) ld,
                                                  assign (deref rd <+> deref d) rd])))))

  (*) (R l) (R r) = R (\k => l (\(lv, ld) =>
                             r (\(rv, rd) => letVal (lv <*> rv) (\x =>
                                             newVar (double 0) (\d =>
                                                  seqs [k (x, d),
                                                  assign ((deref d <*> rv) <+> deref ld) ld,
                                                  assign ((deref d <*> lv) <+> deref rd) rd])))))

  grad f = lam (\x =>  newVar (double 0) (\d => let (R g) = f $ R (\k => k (x, d)) in
                                                seq (g (\(_, d) => assign (double 1) d)) (deref d)))

example : DiffSymantics rep => rep DoubleT -> rep DoubleT
example x = (d 2 * x) + (x * x * x)

test : String
test = compile (grad {rep = Reverse} example)
