module Hoare

-- Based on http://eprints.nottingham.ac.uk/10779/1/Thesis.pdf

Pre : Type -> Type
Pre s = s -> Type

Post : Type -> Type -> Type
Post s a = s -> a -> s -> Type

HoareState : (s : Type) -> Pre s -> (a : Type) -> Post s a -> Type
HoareState s pre a post = (d : DPair s pre) -> DPair (a, s) (\(x, f) => post (fst d) x f)

return : {a : Type} -> (x : a) -> HoareState s (\_ => ()) a (\i, y, f => (i = f, x = y))
return x (st ** ()) = ((x, st) ** (Refl, Refl))

(>>=) : {p1 : Pre s} -> {q1 : Post s a} -> {p2 : a -> Pre s} -> {q2 : a -> Post s b} ->
        HoareState s p1 a q1 ->
        ((x : a) -> HoareState s (p2 x) b (q2 x)) ->
        HoareState s (\s1 => (p1 s1, ((x : a) -> (s2 : s) -> q1 s1 x s2 -> p2 x s2))) b
                     (\s1, x, s3 => DPair (a, s) (\(y,s2) => (q1 s1 y s2, q2 y s2 x s3)))
(>>=) c1 c2 (s1 ** (s1p1, f)) = let ((x, s2) ** p) = (c1 (s1 ** s1p1)) in
                                let ((y, s3) ** q) = c2 x (s2 ** (f x s2 p)) in
                                ((y, s3) ** ((x, s2) ** (p, q)))


get : HoareState s (\_ => ()) s (\i, x, f => (i = f, x = i))
get (st ** ()) = ((st, st) ** (Refl, Refl))

put : (st : s) -> HoareState s (\_ => ()) () (\i, x, f => f = st)
put st _ = (((), st) ** Refl)
