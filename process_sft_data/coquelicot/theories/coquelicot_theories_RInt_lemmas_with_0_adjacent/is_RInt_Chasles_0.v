Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq.
Require Import Continuity Hierarchy.
Section is_RInt.
Context {V : NormedModule R_AbsRing}.
Definition is_RInt (f : R -> V) (a b : R) (If : V) := filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).
Definition ex_RInt (f : R -> V) (a b : R) := exists If : V, is_RInt f a b If.
End is_RInt.
Section StepFun.
Context {V : NormedModule R_AbsRing}.
End StepFun.
Section norm_RInt.
Context {V : NormedModule R_AbsRing}.
End norm_RInt.
Section prod.
Context {U V : NormedModule R_AbsRing}.
End prod.
Section RInt.
Context {V : CompleteNormedModule R_AbsRing}.
Definition RInt (f : R -> V) (a b : R) := iota (is_RInt f a b).
End RInt.

Lemma is_RInt_Chasles_0 (f : R -> V) (a b c : R) (l1 l2 : V) : a < b < c -> is_RInt f a b l1 -> is_RInt f b c l2 -> is_RInt f a c (plus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
case: (ex_RInt_ub f a b).
by exists l1.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ M1 HM1.
case: (ex_RInt_ub f b c).
by exists l2.
rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ M2 HM2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 (pos_div_2 eps))) => {H1} H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 (pos_div_2 eps))) => {H2} H2.
case: H1 => d1 H1.
case: H2 => d2 H2.
move: H1 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ H1.
move: H2 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ H2.
have Hd3 : 0 < eps / (4 * ((M1 + 1) + (M2 + 1))).
apply Rdiv_lt_0_compat.
by apply eps.
repeat apply Rmult_lt_0_compat.
by apply Rlt_0_2.
by apply Rlt_0_2.
apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
have Hd : 0 < Rmin (Rmin d1 d2) (mkposreal _ Hd3).
repeat apply Rmin_case.
by apply d1.
by apply d2.
by apply Hd3.
exists (mkposreal _ Hd) => /= ptd Hstep [Hptd [Hh Hl]].
move: Hh Hl ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => //= _ _ Hh Hl.
rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
rewrite scal_one.
rewrite /ball_norm (double_var eps).
apply Rle_lt_trans with (norm (minus (Riemann_sum f ptd) (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b)))) + norm (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
set v:= minus _ (plus l1 l2).
replace v with (plus (minus (Riemann_sum f ptd) (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b)))) (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
exact: norm_triangle.
rewrite /v /minus -plus_assoc.
apply f_equal.
by rewrite plus_assoc plus_opp_l plus_zero_l.
apply Rplus_lt_compat.
apply Rlt_le_trans with (2 := Rmin_r _ _) in Hstep.
generalize (fun H H0 => Riemann_sum_Chasles_0 f (M1 + 1 + (M2 + 1)) b ptd (mkposreal _ Hd3) H H0 Hptd Hstep).
rewrite /= Hl Hh => H.
replace (eps / 2) with (2 * (mkposreal _ Hd3) * (M1 + 1 + (M2 + 1))).
rewrite -norm_opp opp_plus opp_opp plus_comm.
simpl ; apply H.
intros x Hx.
case: (Rle_lt_dec x b) => Hxb.
apply Rlt_trans with (M1 + 1).
apply Rle_lt_trans with M1.
apply HM1 ; split.
by apply Hx.
by apply Hxb.
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
apply Rlt_trans with (M2 + 1).
apply Rle_lt_trans with M2.
apply HM2 ; split.
by apply Rlt_le, Hxb.
by apply Hx.
apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
apply Rminus_lt_0 ; ring_simplify.
apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
split ; by apply Rlt_le.
simpl ; field.
apply Rgt_not_eq.
apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
apply Rle_trans with (2 := HM1), norm_ge_0.
specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
apply Rle_trans with (2 := HM2), norm_ge_0.
apply Rlt_le_trans with (2 := Rmin_l _ _) in Hstep.
specialize (H1 (SF_cut_down ptd b)).
specialize (H2 (SF_cut_up ptd b)).
apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1) + norm (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
replace (minus (plus (Riemann_sum f (SF_cut_down ptd b)) (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2)) with (plus (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1) (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
apply @norm_triangle.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 2!scal_one /minus opp_plus -2!plus_assoc.
apply f_equal.
rewrite plus_comm -plus_assoc.
apply f_equal.
by apply plus_comm.
rewrite (double_var (eps / 2)) ; apply Rplus_lt_compat.
apply H1.
apply SF_cut_down_step.
rewrite /= Hl Hh ; split ; by apply Rlt_le.
by apply Rlt_le_trans with (1 := Hstep), Rmin_l.
split.
apply SF_cut_down_pointed.
rewrite Hh ; by apply Rlt_le.
by [].
split.
rewrite SF_cut_down_h.
by apply Hh.
rewrite Hh ; by apply Rlt_le.
move: (SF_cut_down_l ptd b) => //=.
apply H2.
apply SF_cut_up_step.
rewrite /= Hl Hh ; split ; by apply Rlt_le.
by apply Rlt_le_trans with (1 := Hstep), Rmin_r.
split.
apply SF_cut_up_pointed.
rewrite Hh ; by apply Rlt_le.
by [].
split.
by rewrite SF_cut_up_h.
move: (SF_cut_up_l ptd b) => /= ->.
by apply Hl.
rewrite Hl ; by apply Rlt_le.
