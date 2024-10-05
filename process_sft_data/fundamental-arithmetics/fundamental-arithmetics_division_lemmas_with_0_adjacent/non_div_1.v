Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma non_div_1 : forall (a:nat),(a<>1)->~(divides 1 a).
intros.
red.
intro.
apply H.
apply divides_antisym;trivial.
apply one_min_div.
