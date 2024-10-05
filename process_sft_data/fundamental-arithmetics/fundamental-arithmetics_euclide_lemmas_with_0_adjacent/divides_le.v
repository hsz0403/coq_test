Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma divides_le : forall (a b:nat),(a<>O)->(divides a b)->(b<=a).
intros.
elim H0;intro q;intro.
replace b with (b*1);try ring.
rewrite H1.
apply mult_le_compat;try omega.
destruct q;omega.
