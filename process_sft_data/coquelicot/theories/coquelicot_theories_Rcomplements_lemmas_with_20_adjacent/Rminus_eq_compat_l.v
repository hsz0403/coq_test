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

Lemma Rmult_minus_distr_r: forall r1 r2 r3 : R, (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
intros.
unfold Rminus.
rewrite <- Ropp_mult_distr_l_reverse.
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

Lemma sum_f_rw_0 (u : nat -> R) (n : nat) : sum_f O n u = sum_f_R0 u n.
Proof.
rewrite /sum_f -minus_n_O.
elim: n => [ | n IH] //.
rewrite /sum_f_R0 -/sum_f_R0 //.
Admitted.

Lemma sum_f_n_Sm (u : nat -> R) (n m : nat) : (n <= m)%nat -> sum_f n (S m) u = sum_f n m u + u (S m).
Proof.
move => H.
rewrite /sum_f -minus_Sn_m // /sum_f_R0 -/sum_f_R0.
rewrite plus_Sn_m.
Admitted.

Lemma sum_f_u_Sk (u : nat -> R) (n m : nat) : (n <= m)%nat -> sum_f (S n) (S m) u = sum_f n m (fun k => u (S k)).
Proof.
move => H ; rewrite /sum_f.
simpl minus.
elim: (m - n)%nat => [ | k IH] //=.
rewrite IH ; repeat apply f_equal.
Admitted.

Lemma sum_f_u_add (u : nat -> R) (p n m : nat) : (n <= m)%nat -> sum_f (n + p)%nat (m + p)%nat u = sum_f n m (fun k => u (k + p)%nat).
Proof.
move => H ; rewrite /sum_f.
rewrite ?(plus_comm _ p) -minus_plus_simpl_l_reverse.
elim: (m - n)%nat => [ | k IH] //=.
by rewrite plus_comm.
rewrite IH ; repeat apply f_equal.
Admitted.

Lemma sum_f_Sn_m (u : nat -> R) (n m : nat) : (n < m)%nat -> sum_f (S n) m u = sum_f n m u - u n.
Proof.
move => H.
elim: m n H => [ | m IH] // n H.
by apply lt_n_O in H.
rewrite sum_f_u_Sk ; try by intuition.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n m u + u (S m) - u n) with ((sum_f n m u - u n) + u (S m)) by ring.
apply lt_n_Sm_le, le_lt_eq_dec in H.
case: H => [ H | -> {n} ] //.
rewrite -IH => //.
rewrite /sum_f ; simpl.
rewrite MyNat.sub_succ_r.
apply lt_minus_O_lt in H.
rewrite -{3}(MyNat.sub_add n m) ; try by intuition.
case: (m-n)%nat H => {IH} [ | k] //= H.
by apply lt_n_O in H.
apply (f_equal (fun y => y + _)).
elim: k {H} => [ | k IH] //.
rewrite /sum_f_R0 -/sum_f_R0 IH ; repeat apply f_equal ; intuition.
Admitted.

Lemma sum_f_R0_skip (u : nat -> R) (n : nat) : sum_f_R0 (fun k => u (n - k)%nat) n = sum_f_R0 u n.
Proof.
suff H : forall n m, (n < m)%nat -> sum_f n m (fun k => u ((m - k) + n)%nat) = sum_f n m u.
case: n => [ | n] //.
move: (H _ _ (lt_O_Sn n)) => {H} H.
rewrite /sum_f in H.
transitivity (sum_f_R0 (fun x : nat => u (S n - (x + 0) + 0)%nat) (S n - 0)).
replace (S n - 0)%nat with (S n) by auto.
elim: {2 4}(S n) => [ | m IH] //.
simpl ; by rewrite plus_0_r.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite ?plus_0_r.
rewrite H.
replace (S n - 0)%nat with (S n) by auto.
elim: (S n) => [ | m IH] //.
rewrite /sum_f_R0 -/sum_f_R0 -IH.
apply f_equal.
by rewrite plus_0_r.
move => {n} n m H.
elim: m u H => [ | m IH] u H //.
apply lt_n_Sm_le, le_lt_eq_dec in H ; case: H IH => [H IH | -> _ {n}] //.
rewrite sum_f_n_Sm ; try by intuition.
replace (sum_f n (S m) u) with (sum_f n (S m) u - u n + u n) by ring.
rewrite -sum_f_Sn_m ; try by intuition.
rewrite sum_f_u_Sk ; try by intuition.
rewrite -(IH (fun k => u (S k))) => {IH} ; try by intuition.
apply f_equal2.
rewrite /sum_f.
elim: {1 3 4}(m - n)%nat (le_refl (m-n)%nat) => [ | k IH] // Hk ; rewrite /sum_f_R0 -/sum_f_R0.
apply f_equal.
rewrite plus_0_l MyNat.sub_add ; intuition.
rewrite IH ; try by intuition.
by rewrite minus_diag plus_0_l.
rewrite /sum_f.
rewrite -minus_Sn_m ; try by intuition.
rewrite minus_diag.
rewrite /sum_f_R0 -/sum_f_R0.
replace (1+m)%nat with (S m) by ring.
Admitted.

Lemma sum_f_chasles (u : nat -> R) (n m k : nat) : (n < m)%nat -> (m < k)%nat -> sum_f (S n) k u = sum_f (S n) m u + sum_f (S m) k u.
Proof.
move => Hnm Hmk.
rewrite ?sum_f_rw //.
ring.
Admitted.

Lemma Rplus_max_distr_l : forall a b c, a + Rmax b c = Rmax (a + b) (a + c).
Proof.
intros a b c.
unfold Rmax.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
Admitted.

Lemma Rplus_max_distr_r : forall a b c, Rmax b c + a = Rmax (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
Admitted.

Lemma Rplus_min_distr_l : forall a b c, a + Rmin b c = Rmin (a + b) (a + c).
Proof.
intros a b c.
unfold Rmin.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
Admitted.

Lemma Rplus_min_distr_r : forall a b c, Rmin b c + a = Rmin (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
Admitted.

Lemma Rmult_max_distr_l : forall a b c, 0 <= a -> a * Rmax b c = Rmax (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmax.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmax ; assert (H := Rle_refl 0).
Admitted.

Lemma Rmult_max_distr_r : forall a b c, 0 <= a -> Rmax b c * a = Rmax (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
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
reflexivity.
