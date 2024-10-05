Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma divides_refl : forall (a:nat),(divides a a).
intros.
red.
exists 1.
auto with arith.
