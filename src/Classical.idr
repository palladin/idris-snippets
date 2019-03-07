module Classical
-- Based on http://www.cs.nott.ac.uk/~psztxa/g53cfr/l06.html/l06.html

import Control.Isomorphism

-- tertium non datur
TND : Type
TND = {P : Type} -> Either P (P -> Void)
-- reductio ad absurdum
RAA : Type
RAA = {P : Type} -> ((P -> Void) -> Void) -> P
-- Pierce's law
Pierce : Type
Pierce = {P, Q : Type} -> ((P -> Q) -> P) -> P

-- ex falso quod libet
efq : {P : Type} -> Void -> P


tndToRaa : TND -> RAA
tndToRaa tnd = f tnd
  where
    f : {P : Type} -> Either P (P -> Void) -> ((P -> Void) -> Void) -> P
    f (Left p) k = p
    f (Right notp) k = efq (k notp)

raaToTnd : RAA -> TND
raaToTnd raa = raa f
  where
    f : {P : Type} -> (Either P (P -> Void) -> Void) -> Void
    f k = k (Right (\p => k (Left p)))

pierceToRaa : Pierce -> RAA
pierceToRaa pierce k = let f' = pierce f in f' (\p => efq (k p))
  where
    f : {P : Type} -> ((((P -> Void) -> P) -> P) -> P) ->
                        ((P -> Void) -> P) -> P
    f _ = pierce

raaToPierce : RAA -> Pierce
raaToPierce raa = raa f
  where
    f : {P, Q : Type} -> ((((P -> Q) -> P) -> P) -> Void) -> Void
    f k = k (\p => p (\q => raa (\_ => k (\_ => q))))
