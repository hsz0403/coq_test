Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma divides_antisym : forall (a b:nat),(divides a b)->(divides b a)->a=b.
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
rewrite H2 in H1.
assert ((a = 0) \/ (q' * q)=1).
apply mult_lemma4.
replace (a*(q'*q)) with (a*q'*q);try (auto with arith).
case H3;intro.
rewrite H4 in H2;simpl in H2;rewrite H2;trivial.
elim (mult_lemma5 q' q H4);intros.
rewrite H5 in H2;rewrite mult_comm in H2;simpl in H2;rewrite plus_comm in H2;simpl in H2;symmetry;trivial.
