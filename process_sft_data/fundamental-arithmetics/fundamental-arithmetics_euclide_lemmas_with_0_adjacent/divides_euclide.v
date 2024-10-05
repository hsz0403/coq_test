Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma divides_euclide : forall (a b:nat)(H:(b<>O)),((divides a b)<->((remainder_euclide a b H)=O)).
intros.
red.
split;intro.
generalize (quo_rem_euclide a b H);intro.
generalize (rem_euclide a b H);intro.
elim H0;intro q;intro.
assert (a=b*q+0).
rewrite plus_comm;simpl;trivial.
assert (0<b);try omega.
generalize (euclide_unique a b (quotient_euclide a b H) (remainder_euclide a b H) q 0 H H1 H4 H2 H5).
intros;tauto.
generalize (quo_rem_euclide a b H).
rewrite H0;rewrite plus_comm;simpl.
intro;exists (quotient_euclide a b H);trivial.
