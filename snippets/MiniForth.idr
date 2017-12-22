module MiniForth

data IxList : {i  : Type} -> (rel : i -> i -> Type) -> i -> i -> Type where
  Nil : IxList rel i i
  (::) : rel i j -> IxList rel j k -> IxList rel i k

data Instr : Nat -> Nat -> Type where
  Lit : Int -> Instr n (S n)
  Dup : Instr (S n) (S (S n))
  Swap : Instr (S (S n)) (S (S n))
  Drop : Instr (S n) n
  Over : Instr (S (S n)) (S (S (S n)))
  Op : (Int -> Int -> Int) -> Instr (S (S n)) (S n)


data Val : Nat -> Nat -> Type where
  ValC : Int -> Val (S n) n


run : IxList Instr i j -> IxList Val i 0 -> IxList Val j 0
run [] st = st
run ((Lit x) :: xs) st = run xs (ValC x :: st)
run (Dup :: xs) ((ValC x) :: st) = run xs (ValC x :: ValC x :: st)
run (Swap :: xs) ((ValC x) :: ((ValC y) :: st)) = run xs (ValC y :: ValC x :: st)
run (Drop :: xs) ((ValC x) :: st) = run xs st
run (Over :: xs) ((ValC x) :: (ValC y) :: st) = run xs ((ValC y) :: (ValC x) :: (ValC y) :: st)
run (Op f :: xs) ((ValC x) :: ((ValC y) :: st)) = run xs (ValC (f x y) :: st)

square : IxList Instr (S n) (S n)
square = Dup :: Op (*) :: Nil

prg : IxList Instr 0 1
prg = Lit 5 :: square


test : IxList Val 1 0
test = run prg []
