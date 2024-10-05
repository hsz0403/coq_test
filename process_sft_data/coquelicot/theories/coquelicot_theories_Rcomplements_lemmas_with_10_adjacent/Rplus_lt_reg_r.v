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

Lemma C_n_n: forall n, C n n = 1.
Proof.
intros n; unfold C.
rewrite minus_diag.
simpl.
field.
Admitted.

Lemma C_n_0: forall n, C n 0 = 1.
Proof.
intros n; unfold C.
rewrite - minus_n_O.
simpl.
field.
Admitted.

Lemma pow2_INR (n : nat) : INR (pow2 n) = 2^n.
Proof.
Admitted.

Lemma pow2_pos (n : nat) : (0 < pow2 n)%nat.
Proof.
apply INR_lt ; rewrite pow2_INR.
Admitted.

Lemma Rinv_le_contravar : forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.
intros x y H1 [H2|H2].
apply Rlt_le.
apply Rinv_lt_contravar with (2 := H2).
apply Rmult_lt_0_compat with (1 := H1).
now apply Rlt_trans with x.
rewrite H2.
Admitted.

Lemma Rinv_lt_cancel (x y : R) : 0 < y -> / y < / x -> x < y.
Proof.
intro Hy ; move/Rlt_not_le => Hxy.
apply Rnot_le_lt ; contradict Hxy.
Admitted.

Lemma Rdiv_1 : forall x : R, x / 1 = x.
Proof.
intros.
unfold Rdiv ; rewrite Rinv_1 Rmult_1_r.
Admitted.

Lemma Rdiv_plus : forall a b c d : R, b <> 0 -> d <> 0 -> a / b + c / d = (a * d + c * b) / (b * d).
Proof.
intros.
field.
split.
apply H0.
Admitted.

Lemma Rdiv_minus : forall a b c d : R, b <> 0 -> d <> 0 -> a / b - c / d = (a * d - c * b) / (b * d).
Proof.
intros.
field.
split.
apply H0.
Admitted.

Lemma Rplus_lt_reg_l (x y z : R) : x + y < x + z -> y < z.
Proof.
Admitted.

Lemma Rle_div_l : forall a b c, c > 0 -> (a / c <= b <-> a <= b * c).
Proof.
split ; intros.
replace a with ((a/c) * c) by (field ; apply Rgt_not_eq, H).
apply Rmult_le_compat_r.
apply Rlt_le, H.
apply H0.
replace b with ((b*c)/c) by (field ; apply Rgt_not_eq, H).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, H.
Admitted.

Lemma Rle_div_r : forall a b c, c > 0 -> (a * c <= b <-> a <= b / c).
Proof.
split ; intros.
replace a with ((a * c) / c) by (field ; apply Rgt_not_eq, H).
apply Rmult_le_compat_r.
apply Rlt_le, Rinv_0_lt_compat, H.
apply H0.
replace b with ((b / c) * c) by (field ; apply Rgt_not_eq, H).
apply Rmult_le_compat_r.
apply Rlt_le, H.
Admitted.

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

Lemma Rplus_lt_reg_r (x y z : R) : y + x < z + x -> y < z.
Proof.
first [ (* 8.4 *) intro H ; apply Rplus_lt_reg_r with x ; now rewrite 2!(Rplus_comm x) | (* 8.5 *) exact: Rplus_lt_reg_r ].
