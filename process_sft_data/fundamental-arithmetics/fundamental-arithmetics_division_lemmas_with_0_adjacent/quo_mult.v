Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma quo_mult : forall (a b:nat)(H:divides a b),forall (n:nat),(b<>O)->(quo (a*n) b (divides_mult b a n H))=n*(quo a b H).
intros.
generalize (quo_is_quo (a*n) b (divides_mult b a n H));intro.
generalize (quo_is_quo a b H);intro.
replace (a*n = b * quo (a * n) b (divides_mult b a n H)) with (b*(quo a b H)*n = b * quo (a * n) b (divides_mult b a n H)) in H1.
symmetry;rewrite mult_comm.
apply mult_lemma6 with b;trivial.
rewrite mult_assoc;trivial.
rewrite <- H2;trivial.
