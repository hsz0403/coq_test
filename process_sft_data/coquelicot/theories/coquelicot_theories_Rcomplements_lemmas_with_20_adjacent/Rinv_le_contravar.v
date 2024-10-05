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

Lemma neq_succ_0 (n : nat) : S n <> 0.
Proof.
move=> contrad.
Admitted.

Lemma sub_succ (n m : nat) : S n - S m = n - m.
Proof.
Admitted.

Lemma sub_succ_l (n m : nat) : n <= m -> S m - n = S (m - n).
Proof.
move=> h.
Admitted.

Lemma lt_neq (n m : nat) : n < m -> n <> m.
Proof.
intros H ->.
Admitted.

Lemma minus_0_le (n m : nat) : n <= m -> n - m = 0.
Proof.
case: (eq_nat_dec n m) => [-> _ | h h'].
by rewrite minus_diag.
apply: not_le_minus_0.
move=> h''.
apply: h.
Admitted.

Lemma sub_succ_r (n m : nat) : n - S m = pred (n - m).
Proof.
case: n => [// | n ].
case: (le_le_S_dec m n) => h; rewrite sub_succ.
rewrite -minus_Sn_m //=.
move: (le_S (S n) m h) => /le_S_n h'.
Admitted.

Lemma sub_add (n m : nat) : n <= m -> m - n + n = m.
Proof.
elim: m => [/le_n_0_eq // | m ih h].
Admitted.

Lemma le_pred_le_succ (n m : nat) : pred n <= m <-> n <= S m.
Proof.
case: n m => /= [ | n m].
split=> _; exact: le_0_n.
split.
exact: le_n_S.
Admitted.

Lemma floor_ex : forall x : R, {n : Z | IZR n <= x < IZR n + 1}.
Proof.
intros.
exists (up (x-1)) ; split.
assert (Rw : x = 1 + (x-1)) ; [ring | rewrite {2}Rw => {Rw}].
assert (Rw :IZR (up (x - 1)) = (IZR (up (x - 1)) - (x - 1)) + (x-1)) ; [ring | rewrite Rw ; clear Rw].
apply Rplus_le_compat_r, (proj2 (archimed _)).
assert (Rw : x = (x-1) + 1) ; [ring | rewrite {1}Rw ; clear Rw].
Admitted.

Lemma floor1_ex : forall x : R, {n : Z | IZR n < x <= IZR n + 1}.
Proof.
intros.
destruct (floor_ex x) as (n,(Hn1,Hn2)).
destruct (Rle_lt_or_eq_dec (IZR n) x Hn1).
exists n ; split.
apply r.
apply Rlt_le, Hn2.
exists (Z.pred n) ; rewrite <- e ; split.
apply IZR_lt, Zlt_pred.
Admitted.

Lemma nfloor_ex : forall x : R, 0 <= x -> {n : nat | INR n <= x < INR n + 1}.
Proof.
intros.
destruct (floor_ex x) as (m,Hm).
destruct (Z_lt_le_dec m 0) as [z|z].
apply Zlt_le_succ in z.
contradict z.
apply Zlt_not_le.
apply lt_IZR.
apply Rle_lt_trans with (1 := H).
rewrite succ_IZR ; apply Hm.
destruct m.
exists O ; apply Hm.
exists (nat_of_P p).
rewrite INR_IZR_INZ.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
apply Hm.
contradict z.
apply Zlt_not_le.
Admitted.

Lemma nfloor1_ex : forall x : R, 0 < x -> {n : nat | INR n < x <= INR n + 1}.
Proof.
intros.
destruct (nfloor_ex x (Rlt_le _ _ H)) as (n,(Hn1,Hn2)).
destruct (Rle_lt_or_eq_dec (INR n) x Hn1).
exists n ; split.
apply r.
apply Rlt_le, Hn2.
destruct n.
contradict H.
rewrite <- e ; simpl ; apply Rlt_irrefl.
exists n ; rewrite <- e ; split.
apply lt_INR, lt_n_Sn.
Admitted.

Lemma INRp1_pos : forall n, 0 < INR n + 1.
Proof.
intros N.
rewrite <- S_INR.
apply lt_0_INR.
Admitted.

Lemma Rlt_nat (x : R) : (exists n : nat, x = INR (S n)) -> 0 < x.
Proof.
intro H ; destruct H.
rewrite H S_INR.
Admitted.

Lemma Rle_pow_lin (a : R) (n : nat) : 0 <= a -> 1 + INR n * a <= (1 + a) ^ n.
Proof.
intro Ha.
induction n.
apply Req_le ; simpl ; ring.
rewrite S_INR.
replace (1 + (INR n + 1) * a) with ((1 + INR n * a) + a) by ring.
apply Rle_trans with ((1 + a) ^ n + a).
apply Rplus_le_compat_r.
exact IHn.
replace ((1+a)^(S n)) with ((1+a)^n + a * (1+a)^n) by (simpl ; ring).
apply Rplus_le_compat_l.
pattern a at 1.
rewrite <- (Rmult_1_r a).
apply Rmult_le_compat_l.
exact Ha.
clear IHn.
apply pow_R1_Rle.
pattern 1 at 1.
rewrite <- (Rplus_0_r 1).
apply Rplus_le_compat_l.
Admitted.

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

Lemma Rplus_lt_reg_r (x y z : R) : y + x < z + x -> y < z.
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

Lemma Rminus_eq_0 : forall r : R, r - r = 0.
Proof.
intros.
Admitted.

Lemma Rdiv_minus_distr : forall a b c, b <> 0 -> a / b - c = (a - b * c) / b.
Proof.
intros.
field.
Admitted.

Lemma Rinv_le_contravar : forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.
intros x y H1 [H2|H2].
apply Rlt_le.
apply Rinv_lt_contravar with (2 := H2).
apply Rmult_lt_0_compat with (1 := H1).
now apply Rlt_trans with x.
rewrite H2.
apply Rle_refl.
