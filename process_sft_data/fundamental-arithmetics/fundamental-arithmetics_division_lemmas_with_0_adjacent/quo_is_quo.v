Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma quo_is_quo : forall (a b:nat)(H:divides a b),a=(mult b (quo a b H)).
intros.
unfold quo.
generalize (quo_dec a b H);intro;elim s;trivial.
