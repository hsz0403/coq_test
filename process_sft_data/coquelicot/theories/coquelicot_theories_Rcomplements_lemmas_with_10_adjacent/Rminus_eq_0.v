Ltac evar_last := match goal with | |- ?f ?x => let tx := type of x in let tx := eval simpl in tx in let tmp := fresh "tmp" in evar (tmp : tx) ; refine (@eq_ind tx tmp f _ x _) ; unfold tmp ; clear tmp end.
Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Module MyNat.
End MyNat.
Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.
Open Scope R_scope.
Definition floor x := proj1_sig (floor_ex x).
Definition floor1 x := proj1_sig (floor1_ex x).
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).
Fixpoint pow2 (n : nat) : nat := match n with | O => 1%nat | S n => (2 * pow2 n)%nat end.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).
Definition sign (x : R) := match total_order_T 0 x with | inleft (left _) => 1 | inleft (right _) => 0 | inright _ => -1 end.
Definition belast {T : Type} (s : seq T) := match s with | [::] => [::] | h :: s => belast h s end.

Lemma Rlt_div_l : forall a b c, c > 0 -> (a / c < b <-> a < b*c).
Proof.
split ; intros.
replace a with ((a/c) * c) by (field ; apply Rgt_not_eq, H).
apply Rmult_lt_compat_r.
apply H.
apply H0.
replace b with ((b*c)/c) by (field ; apply Rgt_not_eq, H).
apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat, H.
Admitted.

Lemma Rlt_div_r : forall a b c, c > 0 -> (a * c < b <-> a < b / c).
Proof.
split ; intros.
replace a with ((a * c) / c) by (field ; apply Rgt_not_eq, H).
apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat, H.
apply H0.
replace b with ((b / c) * c) by (field ; apply Rgt_not_eq, H).
apply Rmult_lt_compat_r.
apply H.
Admitted.

Lemma Rdiv_lt_0_compat : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 0 < r1 / r2.
Proof.
intros r1 r2 H1 H2.
apply Rlt_div_r.
apply H2.
rewrite Rmult_0_l.
Admitted.

Lemma Rdiv_le_0_compat : forall r1 r2 : R, 0 <= r1 -> 0 < r2 -> 0 <= r1 / r2.
Proof.
intros.
apply Rle_div_r.
apply H0.
rewrite Rmult_0_l.
Admitted.

Lemma Rdiv_lt_1 : forall r1 r2, 0 < r2 -> (r1 < r2 <-> r1 / r2 < 1).
Proof.
intros.
pattern r2 at 1.
rewrite <- (Rmult_1_l r2).
Admitted.

Lemma Rdiv_le_1 : forall r1 r2, 0 < r2 -> (r1 <= r2 <-> r1/r2 <= 1).
Proof.
intros.
pattern r2 at 1.
rewrite <- (Rmult_1_l r2).
Admitted.

Lemma Rle_mult_Rlt : forall c a b : R, 0 < b -> c < 1 -> a <= b*c -> a < b.
Proof.
intros.
apply Rle_lt_trans with (1 := H1).
pattern b at 2 ; rewrite <-(Rmult_1_r b).
Admitted.

Lemma Rmult_le_0_r : forall a b, a <= 0 -> 0 <= b -> a * b <= 0.
Proof.
Admitted.

Lemma Rmult_le_0_l : forall a b, 0 <= a -> b <= 0 -> a * b <= 0.
Proof.
Admitted.

Lemma pow2_gt_0 (x : R) : x <> 0 -> 0 < x ^ 2.
Proof.
destruct (pow2_ge_0 x) => // Hx.
contradict Hx.
apply sym_eq, Rmult_integral in H ; case: H => // H.
apply Rmult_integral in H ; case: H => // H.
Admitted.

Lemma Rdiv_minus_distr : forall a b c, b <> 0 -> a / b - c = (a - b * c) / b.
Proof.
intros.
field.
Admitted.

Lemma Rmult_minus_distr_r: forall r1 r2 r3 : R, (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
intros.
unfold Rminus.
rewrite <- Ropp_mult_distr_l_reverse.
Admitted.

Lemma Rminus_eq_compat_l : forall r r1 r2 : R, r1 = r2 <-> r - r1 = r - r2.
Proof.
split ; intros.
apply Rplus_eq_compat_l.
rewrite H.
reflexivity.
replace r1 with (r-(r-r1)) by ring.
replace r2 with (r-(r-r2)) by ring.
apply Rplus_eq_compat_l.
rewrite H.
Admitted.

Lemma Ropp_plus_minus_distr : forall r1 r2 : R, - (r1 + r2) = - r1 - r2.
Proof.
intros.
unfold Rminus.
Admitted.

Lemma Rle_minus_l : forall a b c,(a - c <= b <-> a <= b + c).
Proof.
split ; intros.
replace a with ((a-c)+c) by ring.
apply Rplus_le_compat_r.
apply H.
replace b with ((b+c)-c) by ring.
apply Rplus_le_compat_r.
Admitted.

Lemma Rlt_minus_r : forall a b c,(a < b - c <-> a + c < b).
Proof.
split ; intros.
replace b with ((b-c)+c) by ring.
apply Rplus_lt_compat_r.
apply H.
replace a with ((a+c)-c) by ring.
apply Rplus_lt_compat_r.
Admitted.

Lemma Rlt_minus_l : forall a b c,(a - c < b <-> a < b + c).
Proof.
split ; intros.
replace a with ((a-c)+c) by ring.
apply Rplus_lt_compat_r.
apply H.
replace b with ((b+c)-c) by ring.
apply Rplus_lt_compat_r.
Admitted.

Lemma Rle_minus_r : forall a b c,(a <= b - c <-> a + c <= b).
Proof.
split ; intros.
replace b with ((b-c)+c) by ring.
apply Rplus_le_compat_r.
apply H.
replace a with ((a+c)-c) by ring.
apply Rplus_le_compat_r.
Admitted.

Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a.
Proof.
intros.
pattern a at 1.
rewrite <- (Rplus_0_l a).
Admitted.

Lemma sum_f_rw (a : nat -> R) (n m : nat) : (n < m)%nat -> sum_f (S n) m a = sum_f_R0 a m - sum_f_R0 a n.
Proof.
intro Hnm ; unfold sum_f.
revert a n Hnm.
induction m ; intros a n Hnm.
apply lt_n_O in Hnm ; intuition.
rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl.
revert Hnm ; destruct n ; intro Hnm.
rewrite <- minus_n_O ; simpl ; ring_simplify.
clear Hnm IHm.
induction m ; simpl.
reflexivity.
rewrite <- plus_n_Sm, plus_0_r, IHm ; reflexivity.
rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl ; ring_simplify.
apply lt_S_n in Hnm.
rewrite <- (IHm _ _ Hnm).
clear IHm.
induction (m - S n)%nat ; simpl.
reflexivity.
Admitted.

Lemma Rminus_eq_0 : forall r : R, r - r = 0.
Proof.
intros.
ring.
