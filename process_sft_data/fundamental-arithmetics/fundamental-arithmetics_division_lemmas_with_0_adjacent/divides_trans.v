Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma divides_trans : forall (a b c:nat),(divides a b)->(divides b c)->(divides a c).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
rewrite H2 in H1.
exists (q' * q).
rewrite H1.
auto with arith.
