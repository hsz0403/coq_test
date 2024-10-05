Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma divides_minus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (b-a) d).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
rewrite H1;rewrite H2.
exists (q'-q).
rewrite (mult_comm d q');rewrite (mult_comm d q);rewrite (mult_comm d (q'-q));auto with arith.
