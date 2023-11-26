module Repmin

-- The repmin problem, based on http://www.springerlink.com/content/g74174vvl1861605/

-- Bird's circular program
map : (a -> b) -> Lazy a -> Lazy b
map f l = f l

fix : (Lazy a -> a) -> Lazy a
fix f = loop
  where
    loop : Lazy a
    loop = f loop

trace : (a -> Lazy b -> (c, b)) -> a -> c
trace f x = fst $ fix (\rec => f x (map snd rec))

data Tree a = Leaf a | Branch (Tree a) (Tree a)

copy : Tree Int -> Lazy Int -> (Tree (Lazy Int), Int)
copy (Leaf x) l = (Leaf l, x)
copy (Branch x y) l = let (tl, ml) = copy x l
                          (tr, mr) = copy y l in
                          (Branch tl tr, min ml mr)

repmin : Tree Int -> Tree (Lazy Int)
repmin t = trace copy t

print : Tree (Lazy Int) -> String
print (Leaf x) = "L " ++ (show x)
print (Branch x y) = "(B " ++ print x ++ " " ++ print y ++ ")"

test : String
test = print . repmin $ Branch (Branch (Leaf 0) (Leaf 2)) (Leaf 1)

-- Pettorossi's higher-order program 
repmin' : Tree Int -> Tree Int
repmin' t = let (f, m) = aux t in f m
  where
    aux : Tree Int -> (Int -> Tree Int, Int)
    aux (Leaf x) = (\m => Leaf m, x)
    aux (Branch l r) = let (fl, ml) = aux l
                           (fr, mr) = aux r in
                           (\m => Branch (fl m) (fr m), min ml mr)

test' : repmin' (Branch (Branch (Leaf 0) (Leaf 2)) (Leaf 1)) = Branch (Branch (Leaf 0) (Leaf 0)) (Leaf 0)
test' = Refl
