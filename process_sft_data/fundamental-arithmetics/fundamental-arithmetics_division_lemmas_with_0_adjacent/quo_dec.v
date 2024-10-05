Require Import missing.
Require Import Wf_nat.
Definition divides (a b:nat) := exists q:nat,a = (b*q).
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

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
apply (divides_minus b b (S n0));[apply divides_refl | trivial].
