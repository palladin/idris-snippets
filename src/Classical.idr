module Classical
-- Based on http://www.cs.nott.ac.uk/~psztxa/g53cfr/l06.html/l06.html

-- tertium non datur
TND : Type
TND = (P : Type) -> Either P (P -> Void)
-- reductio ad absurdum
RAA : Type
RAA = (P : Type) -> ((P -> Void) -> Void) -> P
-- Pierce's law
Pierce : Type
Pierce = (P, Q : Type) -> ((P -> Q) -> P) -> P

-- ex falso quod libet
efq : (P : Type) -> Void -> P


tndToRaa : TND -> RAA
tndToRaa tnd P = f (tnd P)
  where
    f : Either P (P -> Void) -> ((P -> Void) -> Void) -> P
    f (Left p) k = p
    f (Right notp) k = efq P (k notp)

raaToTnd : RAA -> TND
raaToTnd raa P = raa (Either P (P -> Void)) (\k => k (Right (\p => k (Left p))))


pierceToRaa : Pierce -> RAA
pierceToRaa pierce P k = pierce (((P -> Void) -> P) -> P) P (\_ => pierce P Void) (\x => efq P (k x))


raaToPierce : RAA -> Pierce
raaToPierce raa P _Q = raa (((P -> _Q) -> P) -> P) (\k => k (\p => p (\q => raa _Q (\_ => k (\_ => q)))))
