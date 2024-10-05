Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma divides_dec : forall (a b:nat),{divides a b}+{~(divides a b)}.
intros.
case (eq_nat_dec b 0).
case (eq_nat_dec a 0);intros.
rewrite e;left;apply zero_max_div.
right;rewrite e;intro.
elim H;intro q;intro.
simpl in H0;apply n;trivial.
intro.
case (eq_nat_dec (remainder_euclide a b n) 0);[left | right];intros;elim (divides_euclide a b n);auto.
