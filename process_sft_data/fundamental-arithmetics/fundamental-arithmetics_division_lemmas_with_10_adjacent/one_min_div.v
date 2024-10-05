Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

Lemma zero_max_div : forall (n:nat),(divides O n).
intros.
red.
exists O.
Admitted.

Lemma divides_refl : forall (a:nat),(divides a a).
intros.
red.
exists 1.
Admitted.

Lemma divides_trans : forall (a b c:nat),(divides a b)->(divides b c)->(divides a c).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
rewrite H2 in H1.
exists (q' * q).
rewrite H1.
Admitted.

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
Admitted.

Lemma non_div_1 : forall (a:nat),(a<>1)->~(divides 1 a).
intros.
red.
intro.
apply H.
apply divides_antisym;trivial.
Admitted.

Lemma divides_plus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (plus a b) d).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
exists (q+q').
rewrite H1;rewrite H2.
Admitted.

Lemma divides_mult : forall (d a b:nat),(divides a d)->(divides (a*b) d).
unfold divides.
intros.
elim H;intro q;intro.
exists (b * q).
rewrite H0.
Admitted.

Lemma divides_minus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (b-a) d).
unfold divides.
intros.
elim H;intro q;intro.
elim H0;intro q';intro.
rewrite H1;rewrite H2.
exists (q'-q).
Admitted.

Lemma quo_dec : forall (a b:nat),(divides a b)->{q:nat | a=b*q}.
intros.
apply (lt_wf_rec a (fun x:nat => (divides x b)->{q:nat | x = b*q}));trivial.
intro.
case n;intros.
exists 0;auto with arith.
elim (H0 ((S n0)-b)).
intro q;intro.
exists (S q).
replace (S n0) with (b+(S n0-b)).
rewrite p;rewrite plus_comm;auto with arith.
symmetry.
apply le_plus_minus.
elim H1;intros.
rewrite H2.
replace (b <= b*x) with (1*b <= b*x);rewrite (mult_comm b x).
apply mult_le_compat_r.
destruct x;[rewrite mult_comm in H2;discriminate | auto with arith].
simpl;auto with arith.
destruct b.
elim H1;simpl;intros;discriminate.
omega.
Admitted.

Lemma quo_is_quo : forall (a b:nat)(H:divides a b),a=(mult b (quo a b H)).
intros.
unfold quo.
Admitted.

Lemma one_min_div : forall (n:nat),(divides n 1).
intros.
red.
exists n.
auto with arith.
