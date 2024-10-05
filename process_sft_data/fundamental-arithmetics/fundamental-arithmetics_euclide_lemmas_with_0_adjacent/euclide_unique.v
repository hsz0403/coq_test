Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma euclide_unique : forall (a b q r q' r':nat),(b<>O)->a=b*q+r->a=b*q'+r'->r<b->r'<b->(q=q')/\(r=r').
intros.
rewrite H1 in H0.
case (lt_eq_lt_dec q q');intro.
case s;intro.
rewrite (le_plus_minus q q') in H0;try (auto with arith).
rewrite mult_plus_distr_l in H0.
assert (b*(q'-q)+r' = r).
apply plus_reg_l with (b*q).
rewrite plus_assoc;trivial.
assert (0<(q'-q));try omega.
assert (b<=b*(q'-q));try omega.
case (mult_O_le b (q'-q));intro;try omega.
rewrite mult_comm;trivial.
split;try tauto.
rewrite <- e in H0.
symmetry;apply plus_reg_l with (b*q);trivial.
rewrite (le_plus_minus q' q) in H0;try (auto with arith).
rewrite mult_plus_distr_l in H0.
assert (r'=(b*(q-q')+r)).
apply plus_reg_l with (b*q').
rewrite plus_assoc;trivial.
assert (0<(q-q'));try omega.
assert (b<=b*(q-q'));try omega.
case (mult_O_le b (q-q'));intro;try omega.
rewrite mult_comm;trivial.
