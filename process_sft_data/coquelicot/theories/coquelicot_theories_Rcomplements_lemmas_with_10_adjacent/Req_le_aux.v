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

Lemma Rabs_eq_0 : forall x, Rabs x = 0 -> x = 0.
Proof.
intros.
unfold Rabs in H.
destruct Rcase_abs.
rewrite <- (Ropp_involutive x).
apply Ropp_eq_0_compat.
apply H.
Admitted.

Lemma Rabs_le_between : forall x y, (Rabs x <= y <-> -y <= x <= y).
Proof.
split.
split.
rewrite <-(Ropp_involutive x).
apply Ropp_le_contravar.
apply (Rle_trans _ (Rabs x)).
rewrite <-Rabs_Ropp.
apply RRle_abs.
apply H.
apply (Rle_trans _ (Rabs x)).
apply RRle_abs.
apply H.
intros.
unfold Rabs.
destruct (Rcase_abs x).
rewrite <-(Ropp_involutive y).
apply Ropp_le_contravar.
apply H.
Admitted.

Lemma Rabs_le_between' : forall x y z, Rabs (x - y) <= z <-> y-z <= x <= y+z.
Proof.
split ; intros.
cut (-z <= x-y <= z).
intros ; split.
rewrite <- (Rplus_0_l x).
rewrite <-(Rplus_opp_r y).
rewrite Rplus_assoc.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
apply H0.
rewrite <- (Rplus_0_l x).
rewrite <-(Rplus_opp_r y).
rewrite Rplus_assoc.
apply Rplus_le_compat_l.
rewrite Rplus_comm.
apply H0.
apply (Rabs_le_between (x-y) z).
apply H.
apply (Rabs_le_between (x-y) z).
split.
rewrite <- (Rplus_0_r (-z)).
rewrite <-(Rplus_opp_r y).
rewrite <- Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
apply H.
rewrite <- (Rplus_0_r z).
rewrite <-(Rplus_opp_r y).
rewrite <- Rplus_assoc.
apply Rplus_le_compat_r.
rewrite Rplus_comm.
Admitted.

Lemma Rabs_lt_between : forall x y, (Rabs x < y <-> -y < x < y).
Proof.
split.
intros; split; now apply Rabs_def2.
Admitted.

Lemma Rabs_lt_between' : forall x y z, Rabs (x - y) < z <-> y-z < x < y+z.
Proof.
split ; intros.
cut (-z < x-y < z).
intros ; split.
rewrite <- (Rplus_0_l x).
rewrite <-(Rplus_opp_r y).
rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
rewrite Rplus_comm.
apply H0.
rewrite <- (Rplus_0_l x).
rewrite <-(Rplus_opp_r y).
rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
rewrite Rplus_comm.
apply H0.
apply (Rabs_lt_between (x-y) z).
apply H.
apply (Rabs_lt_between (x-y) z).
split.
rewrite <- (Rplus_0_r (-z)).
rewrite <-(Rplus_opp_r y).
rewrite <- Rplus_assoc.
apply Rplus_lt_compat_r.
rewrite Rplus_comm.
apply H.
rewrite <- (Rplus_0_r z).
rewrite <-(Rplus_opp_r y).
rewrite <- Rplus_assoc.
apply Rplus_lt_compat_r.
rewrite Rplus_comm.
Admitted.

Lemma Rabs_le_between_min_max : forall x y z, Rmin x y <= z <= Rmax x y -> Rabs (z - y) <= Rabs (x - y).
Proof.
intros x y z H.
case (Rle_or_lt x y); intros H'.
rewrite Rmin_left in H;[idtac|exact H'].
rewrite Rmax_right in H;[idtac|exact H'].
rewrite Rabs_left1.
rewrite Rabs_left1.
apply Ropp_le_contravar.
apply Rplus_le_compat_r.
apply H.
apply Rle_minus; exact H'.
apply Rle_minus; apply H.
rewrite Rmin_right in H;[idtac|left; exact H'].
rewrite Rmax_left in H;[idtac|left; exact H'].
rewrite Rabs_right.
rewrite Rabs_right.
apply Rplus_le_compat_r.
apply H.
apply Rge_minus; left; apply H'.
Admitted.

Lemma Rabs_le_between_Rmax : forall x m M, m <= x <= M -> Rabs x <= Rmax M (-m).
Proof.
intros x m M Hx.
unfold Rabs ; destruct Rcase_abs as [H|H].
apply Rle_trans with (2 := RmaxLess2 _ _).
apply Ropp_le_contravar, Hx.
apply Rle_trans with (2 := RmaxLess1 _ _).
Admitted.

Lemma Rabs_lt_between_Rmax : forall x m M, m < x < M -> Rabs x < Rmax M (-m).
Proof.
intros x m M Hx.
unfold Rabs ; destruct Rcase_abs as [H|H].
apply Rlt_le_trans with (2 := RmaxLess2 _ _).
apply Ropp_lt_contravar, Hx.
apply Rlt_le_trans with (2 := RmaxLess1 _ _).
Admitted.

Lemma Rabs_maj2 : forall x, -x <= Rabs x.
Proof.
intros.
rewrite <- Rabs_Ropp.
Admitted.

Lemma Req_lt_aux : forall x y, (forall eps : posreal, Rabs (x - y) < eps) -> x = y.
Proof.
intros.
apply Rminus_diag_uniq.
apply Rabs_eq_0.
apply Rle_antisym.
apply le_epsilon.
intros.
rewrite Rplus_0_l.
apply Rlt_le.
apply (H (mkposreal eps H0)).
Admitted.

Lemma is_pos_div_2 (eps : posreal) : 0 < eps / 2.
Proof.
Admitted.

Lemma sign_0 : sign 0 = 0.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
elim (Rlt_irrefl _ H).
exact H.
Admitted.

Lemma sign_opp (x : R) : sign (-x) = - sign x.
Proof.
unfold sign.
Admitted.

Lemma sign_eq_1 (x : R) : 0 < x -> sign x = 1.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_eq_m1 (x : R) : x < 0 -> sign x = -1.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_le (x y : R) : x <= y -> sign x <= sign y.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_ge_0 (x : R) : 0 <= x -> 0 <= sign x.
Proof.
intros Hx.
rewrite <- sign_0.
Admitted.

Lemma sign_le_0 (x : R) : x <= 0 -> sign x <= 0.
Proof.
intros Hx.
rewrite <- sign_0.
Admitted.

Lemma sign_neq_0 (x : R) : x <> 0 -> sign x <> 0.
Proof.
intros Hx.
unfold sign.
Admitted.

Lemma sign_mult (x y : R) : sign (x * y) = sign x * sign y.
Proof.
wlog: x / (0 < x) => [Hw | Hx].
case: (Rle_lt_dec 0 x) => Hx.
case: Hx => Hx.
by apply Hw.
rewrite -Hx Rmult_0_l.
rewrite sign_0.
by rewrite Rmult_0_l.
rewrite -(Ropp_involutive x).
rewrite sign_opp Ropp_mult_distr_l_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
wlog: y / (0 < y) => [Hw | Hy].
case: (Rle_lt_dec 0 y) => Hy.
case: Hy => Hy.
by apply Hw.
rewrite -Hy Rmult_0_r.
rewrite sign_0.
by rewrite Rmult_0_r.
rewrite -(Ropp_involutive y).
rewrite sign_opp Ropp_mult_distr_r_reverse sign_opp Hw.
ring.
by apply Ropp_0_gt_lt_contravar.
have Hxy : 0 < x * y.
by apply Rmult_lt_0_compat.
rewrite -> 3!sign_eq_1 by easy.
Admitted.

Lemma Req_le_aux : forall x y, (forall eps : posreal, Rabs (x - y) <= eps) -> x = y.
Proof.
intros.
apply Rminus_diag_uniq.
apply Rabs_eq_0.
apply Rle_antisym.
apply le_epsilon.
intros.
rewrite Rplus_0_l.
apply (H (mkposreal eps H0)).
apply Rabs_pos.
