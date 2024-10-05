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

Lemma Rmult_min_distr_l : forall a b c, 0 <= a -> a * Rmin b c = Rmin (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmin.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmin ; assert (H := Rle_refl 0).
Admitted.

Lemma Rmult_min_distr_r : forall a b c, 0 <= a -> Rmin b c * a = Rmin (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
Admitted.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) = Rmin (Rmin x y) z.
intros x y z; unfold Rmin.
destruct (Rle_dec y z); destruct (Rle_dec x y); destruct (Rle_dec x z); destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
Admitted.

Lemma Rmax_assoc : forall x y z, Rmax x (Rmax y z) = Rmax (Rmax x y) z.
intros x y z; unfold Rmax.
destruct (Rle_dec y z); destruct (Rle_dec x y); destruct (Rle_dec x z); destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
Admitted.

Lemma Rmax_le_compat : forall a b c d, a <= b -> c <= d -> Rmax a c <= Rmax b d.
Proof.
intros.
unfold Rmax.
destruct (Rle_dec a c).
destruct (Rle_dec b d).
apply H0.
apply Rnot_le_lt in n.
apply (Rle_trans _ d).
apply H0.
apply (Rlt_le _ _ n).
destruct (Rle_dec b d).
apply (Rle_trans _ b).
apply H.
apply r.
Admitted.

Lemma Rmax_opp_Rmin : forall a b, Rmax (-a) (-b) = - Rmin a b.
Proof.
intros.
destruct (Rle_or_lt a b).
rewrite Rmax_left.
rewrite Rmin_left.
reflexivity.
apply H.
apply Ropp_le_contravar.
apply H.
rewrite Rmax_right.
rewrite Rmin_right.
reflexivity.
apply Rlt_le, H.
apply Ropp_le_contravar.
apply Rlt_le.
Admitted.

Lemma Rmin_opp_Rmax : forall a b, Rmin (-a) (-b) = - Rmax a b.
Proof.
intros.
rewrite Rmax_comm.
unfold Rmin ; case Rle_dec ; intro Hab.
apply Ropp_le_cancel in Hab.
unfold Rmax ; case Rle_dec ; intuition.
apply Rnot_le_lt, Ropp_lt_cancel, Rlt_not_le in Hab.
Admitted.

Lemma Rmax_mult : forall a b c, 0 <= c -> Rmax a b * c = Rmax (a * c) (b * c).
Proof.
intros.
repeat rewrite (Rmult_comm _ c).
apply sym_eq.
apply RmaxRmult.
Admitted.

Lemma Rplus_le_Rmax : forall a b : R, a + b <= 2*Rmax a b.
Proof.
intros.
rewrite RIneq.double.
destruct (Rle_lt_dec a b).
rewrite Rmax_right.
apply Rplus_le_compat_r.
apply r.
apply r.
rewrite Rmax_left.
apply Rplus_le_compat_l.
apply Rlt_le.
apply r.
Admitted.

Lemma Rmin_Rmax_l : forall a b, Rmin a b <= a <= Rmax a b.
Proof.
split.
apply Rmin_l.
Admitted.

Lemma Rmin_Rmax_r : forall a b, Rmin a b <= b <= Rmax a b.
Proof.
split.
apply Rmin_r.
Admitted.

Lemma Rmin_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
intros.
Admitted.

Lemma Rabs_div : forall a b : R, b <> 0 -> Rabs (a/b) = (Rabs a) / (Rabs b).
Proof.
intros.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv.
reflexivity.
Admitted.

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

Lemma Rmax_le_Rplus : forall a b : R, 0 <= a -> 0 <= b -> Rmax a b <= a + b.
Proof.
intros.
destruct (Rle_lt_dec a b).
rewrite <- (Rplus_0_l (Rmax a b)).
rewrite Rmax_right.
apply Rplus_le_compat_r.
apply H.
apply r.
rewrite <- (Rplus_0_r (Rmax a b)).
rewrite Rmax_left.
apply Rplus_le_compat_l.
apply H0.
apply Rlt_le, r.
