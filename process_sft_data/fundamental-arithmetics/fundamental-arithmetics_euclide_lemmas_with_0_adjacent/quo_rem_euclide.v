Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma quo_rem_euclide : forall (a b:nat)(H:(b<>O)),a=b*(quotient_euclide a b H)+(remainder_euclide a b H).
unfold quotient_euclide;unfold remainder_euclide;intros.
generalize (euclide a b H);intros.
elim s;intro q;intro.
elim p;intro r;intro.
tauto.
