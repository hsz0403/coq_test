Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma is_RInt_PSeries (a : nat -> R) (x : R) : Rbar_lt (Rabs x) (CV_radius a) -> is_RInt (PSeries a) 0 x (PSeries (PS_Int a) x).
Proof.
move => Hx.
have H : forall y, Rmin 0 x <= y <= Rmax 0 x -> Rbar_lt (Rabs y) (CV_radius a).
move => y Hy.
apply: Rbar_le_lt_trans Hx.
apply Rabs_le_between.
split.
apply Rle_trans with (2 := proj1 Hy).
rewrite /Rabs /Rmin.
case: Rcase_abs ; case: Rle_dec => // Hx Hx' ; rewrite ?Ropp_involutive.
by apply Rlt_le.
by apply Req_le.
apply Ropp_le_cancel ; by rewrite Ropp_involutive Ropp_0.
by apply Rge_le in Hx'.
apply Rle_trans with (1 := proj2 Hy).
rewrite /Rabs /Rmax.
case: Rcase_abs ; case: Rle_dec => // Hx Hx'.
by apply Rlt_not_le in Hx'.
apply Ropp_le_cancel, Rlt_le ; by rewrite Ropp_involutive Ropp_0.
by apply Req_le.
by apply Rge_le in Hx'.
apply is_RInt_ext with (Derive (PSeries (PS_Int a))).
move => y Hy.
rewrite Derive_PSeries.
apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
field.
apply Rgt_not_eq, INRp1_pos.
rewrite CV_radius_Int.
by apply H ; split ; apply Rlt_le ; apply Hy.
evar_last.
apply: is_RInt_derive.
move => y Hy.
apply Derive_correct, ex_derive_PSeries.
rewrite CV_radius_Int.
by apply H.
move => y Hy.
apply continuous_ext_loc with (PSeries a).
apply locally_interval with (Rbar_opp (CV_radius a)) (CV_radius a).
apply Rbar_opp_lt ; rewrite Rbar_opp_involutive.
apply: Rbar_le_lt_trans (H _ Hy).
apply Rabs_maj2.
apply: Rbar_le_lt_trans (H _ Hy).
apply Rle_abs.
move => z Hz Hz'.
rewrite Derive_PSeries.
apply PSeries_ext ; rewrite /PS_derive /PS_Int => n ; rewrite S_INR.
field.
apply Rgt_not_eq, INRp1_pos.
rewrite CV_radius_Int.
apply (Rbar_abs_lt_between z) ; by split.
apply continuity_pt_filterlim, PSeries_continuity.
by apply H.
rewrite PSeries_0 /(PS_Int _ 0) ; by rewrite minus_zero_r.
