Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma divides_plus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (plus a b) d).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
exists (q+q').
rewrite H1;rewrite H2.
ring.
