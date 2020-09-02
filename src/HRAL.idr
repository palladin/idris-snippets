module HRAL

-- Based on https://www.cambridge.org/core/services/aop-cambridge-core/content/view/CC82B2E79DC5CCAD57E0AC5DF0D43DEC/S0956796820000064a.pdf/div-class-title-heterogeneous-binary-random-access-lists-div.pdf

data Tree : Type -> Nat -> Type where
  Leaf : a -> Tree a Z
  Node : Tree a n -> Tree a n -> Tree a (S n)

data Path : Nat -> Type where
  Here : Path Z
  Left : Path n -> Path (S n)
  Right : Path n -> Path (S n)

namespace Tree
  lookup : Tree a n -> Path n -> a
  lookup (Leaf x) Here = x
  lookup (Node t1 t2) (Left p) = lookup t1 p
  lookup (Node t1 t2) (Right p) = lookup t2 p


data Bin : Type where
  End : Bin
  One : Bin -> Bin
  Zero : Bin -> Bin

bsucc : Bin -> Bin
bsucc End = One End
bsucc (One b) = Zero (bsucc b)
bsucc (Zero b) = One b

data RAL : Type -> Nat -> Bin -> Type where
  Nil : RAL a n End
  Cons1 : Tree a n -> RAL a (S n) b -> RAL a n (One b)
  Cons0 : RAL a (S n) b -> RAL a n (Zero b)

data Pos : Nat -> Bin -> Type where
  PosHere : Path n -> Pos n (One b)
  There0 : Pos (S n) b -> Pos n (Zero b)
  There1 : Pos (S n) b -> Pos n (One b)

namespace RAL
  lookup : RAL a n b -> Pos n b -> a
  lookup [] (PosHere _) impossible
  lookup [] (There0 _) impossible
  lookup [] (There1 _) impossible
  lookup (Cons1 t r) (PosHere p) = Tree.lookup t p
  lookup (Cons1 t r) (There1 p) = lookup r p
  lookup (Cons0 r) (There0 p) = lookup r p

  consTree : Tree a n -> RAL a n b -> RAL a n (bsucc b)
  consTree t [] = Cons1 t Nil
  consTree t (Cons1 t' r) = Cons0 (consTree (Node t t') r)
  consTree t (Cons0 r) = Cons1 t r

  cons : a -> RAL a Z b -> RAL a Z (bsucc b)
  cons x r = consTree (Leaf x) r

data HTree : Tree Type n -> Type where
  HLeaf : u -> HTree (Leaf u)
  HNode : HTree us -> HTree vs -> HTree (Node us vs)

data HPath : Tree Type n -> Type -> Type where
  HHere : HPath (Leaf u) u
  HLeft : HPath us u -> HPath (Node us vs) u
  HRight : HPath vs u -> HPath (Node us vs) u

namespace HTree
  lookup : HTree us -> HPath us u -> u
  lookup (HLeaf u) HHere = u
  lookup (HNode t1 t2) (HLeft p) = lookup t1 p
  lookup (HNode t1 t2) (HRight p) = lookup t2 p

data HRAL : RAL Type n b -> Type where
  HNil : HRAL Nil
  HCons1 : HTree t -> HRAL r -> HRAL (Cons1 t r)
  HCons0 : HRAL r -> HRAL (Cons0 r)

data HPos : RAL Type n b -> Type -> Type where
  HPosHere : HPath t u -> HPos (Cons1 t r) u
  HThere0 : HPos r u -> HPos (Cons0 r) u
  HThere1 : HPos r u -> HPos (Cons1 t r) u

namespace HRAL
  lookup : HRAL r -> HPos r u -> u
  lookup HNil (HPosHere _) impossible
  lookup HNil (HThere0 _) impossible
  lookup HNil (HThere1 _) impossible
  lookup (HCons1 t r) (HPosHere p) = HTree.lookup t p
  lookup (HCons1 t r) (HThere1 p) = lookup r p
  lookup (HCons0 r) (HThere0 p) = lookup r p

  consTree : HTree t -> HRAL r -> HRAL (RAL.consTree t r)
  consTree t HNil = HCons1 t HNil
  consTree t (HCons1 t' r) = HCons0 (consTree (HNode t t') r)
  consTree t (HCons0 r) = HCons1 t r

  cons : (u : Type) -> HRAL r -> HRAL (RAL.cons Type r)
  cons x r = consTree (HLeaf x) r
