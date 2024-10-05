Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Theorem euclide : forall (a b:nat),(b<>O)->{q:nat & { r:nat | (a=b*q+r) /\ (r < b)}}.
intros.
apply (lt_wf_rec a (fun a:nat =>{q : nat & {r : nat | a = b * q + r /\ r < b}})).
intros.
case (le_lt_dec b n);intro.
elim (H0 (n-b)).
intro q;intro.
elim p;intro r;intro.
exists (q+1);exists r.
split;try tauto.
rewrite (le_plus_minus b n);trivial.
elim p0;intros.
rewrite H1;ring.
omega.
exists 0;exists n.
split;try tauto.
ring.
