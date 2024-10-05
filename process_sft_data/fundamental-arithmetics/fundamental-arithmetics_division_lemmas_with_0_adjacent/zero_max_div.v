Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma zero_max_div : forall (n:nat),(divides O n).
intros.
red.
exists O.
auto with arith.
