module Matrix

data Shape : Type where
  Zero : Shape
  One : Shape
  Either : Shape -> Shape -> Shape


data Matrix : (e : Type) -> (c : Shape) -> (r : Shape) -> Type where
  One' : e -> Matrix e One One
  Join : Matrix e a r -> Matrix e b r -> Matrix e (Either a b) r
  Fork : Matrix e c a -> Matrix e c b -> Matrix e c (Either a b)

comp : Num e => Matrix e cr rows -> Matrix e cols cr -> Matrix e cols rows

prf : 2 = Z -> Void
prf Refl impossible

fromNat : Nat -> Shape
fromNat Z = Zero
fromNat (S Z) = One
fromNat n with (modNat n 2 == 0, fromNat $ modNatNZ n 2 prf)
  fromNat n | (True, m)  = Either m m
  fromNat n | (False, m)  = Either One $ Either m m
