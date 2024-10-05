Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.
Definition Bessel1_seq (n k : nat) := (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).
Definition Bessel1 (n : nat) (x : R) := (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma Bessel1_uniqueness_aux_1 (a : nat -> R) (n : nat) : (a 0%nat = 0 \/ n = O) -> (a 1%nat = 0 \/ n = 1%nat) -> (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0) -> (forall k : nat, (k < n)%nat -> a k = 0) /\ (forall p : nat, a (n + 2 * p + 1)%nat = 0) /\ (forall p : nat, a (n + 2 * p)%nat = Bessel1_seq n p * / 2 ^ (2 * p) * INR (fact n) * a n).
Proof.
intros Ha0 Ha1 Ha.
assert (forall k, S (S k) <> n -> a (S (S k)) = - a k / (INR (S (S k)) ^ 2 - INR n ^ 2)).
intros k Hk.
replace (a k) with (- (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k))).
field.
replace (INR (S (S k)) ^ 2 - INR n ^ 2) with ((INR (S (S k)) - INR n) * (INR (S (S k)) + INR n)) by ring.
apply Rmult_integral_contrapositive_currified.
apply Rminus_eq_contra.
by apply not_INR.
rewrite -plus_INR plus_Sn_m.
by apply (not_INR _ O), sym_not_eq, O_S.
replace (a k) with ((INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k - (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k))) by ring.
rewrite Ha ; ring.
assert (forall k : nat, (k < n)%nat -> a k = 0).
destruct n => k Hk.
by apply lt_n_O in Hk.
case: Ha0 => // Ha0.
destruct n.
destruct k => //.
by apply lt_S_n, lt_n_O in Hk.
case: Ha1 => // Ha1.
move: k Hk.
apply (Div2.ind_0_1_SS (fun k => (k < S (S n))%nat -> a k = 0)) => // k IH Hk.
rewrite H.
rewrite IH /Rdiv.
ring.
eapply lt_trans, Hk.
eapply lt_trans ; apply lt_n_Sn.
by apply MyNat.lt_neq.
repeat split.
by [].
elim => [ | p IH].
replace (n + 2 * 0 + 1)%nat with (S n) by ring.
destruct n => //=.
case: Ha1 => // Ha1.
case: Ha0 => // Ha0.
rewrite H ; try by intuition.
rewrite H0 /Rdiv.
ring.
by apply lt_n_Sn.
replace (n + 2 * S p + 1)%nat with (S (S (n + 2 * p + 1)%nat)) by ring.
rewrite H ; try by intuition.
rewrite IH /Rdiv.
ring.
elim => [ | p IH].
replace (n + 2 * 0)%nat with (n) by ring.
rewrite /Bessel1_seq /= -plus_n_O.
field ; by apply INR_fact_neq_0.
replace (n + 2 * S p)%nat with (S (S (n + 2 * p)%nat)) by ring.
rewrite H ; try by intuition.
rewrite IH /Rdiv.
rewrite /Bessel1_seq -plus_n_Sm.
rewrite !pow_sqr /fact -/fact !mult_INR !S_INR !plus_INR /=.
field ; rewrite -!plus_INR -!S_INR ; repeat split ; try (by apply INR_fact_neq_0) ; try (by apply (not_INR _ 0), sym_not_eq, O_S).
apply pow_nonzero, Rgt_not_eq ; apply Rmult_lt_0_compat ; by apply Rlt_0_2.
rewrite -Rsqr_plus_minus.
apply Rmult_integral_contrapositive_currified.
rewrite -plus_INR.
apply Rgt_not_eq, lt_0_INR.
lia.
apply Rminus_eq_contra, not_INR.
lia.
