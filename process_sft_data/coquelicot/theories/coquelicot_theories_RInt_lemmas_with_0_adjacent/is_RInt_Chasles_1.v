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

Lemma is_RInt_Chasles_1 (f : R -> V) (a b c : R) l1 l2 : a < b < c -> is_RInt f a c l1 -> is_RInt f b c l2 -> is_RInt f a b (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => {H1} d1 /= H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => {H2} d2 /= H2.
exists d1 ; simpl ; intros y Hstep [Hptd [Hh Hl]].
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\ pointed_subdiv y /\ SF_h y = Rmin b c /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax b c).
apply filter_ex.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
repeat (split => //=).
by apply H5.
by apply H6.
case: H => y2 [Hstep2 H].
specialize (H2 y2 (Rlt_le_trans _ _ _ Hstep2 (Rmin_r _ _)) H).
case: H => Hptd2 [Hh2 Hl2].
set y1 := mkSF_seq (SF_h y) (SF_t y ++ SF_t y2).
move: Hl Hh2 Hh Hl2 H1 H2 ; rewrite /Rmax /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) (Rlt_le _ _ Hbc) => // _ _ ; case: Rle_dec => // _ _.
case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => // _ _.
move => Hl Hh2 Hh Hl2 H1 H2.
rewrite -Hl in Hab, Hbc, H2, Hh2 |-* => {b Hl}.
rewrite -Hh in H1, Hab |- * => {a Hh}.
rewrite -Hl2 in Hbc, H2, H1 => {c Hl2}.
assert (seq_step (SF_lx y1) < d1).
unfold y1 ; move: Hstep Hh2.
clear -Hstep2.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hstep Hl.
rewrite -Hl.
by apply Rlt_le_trans with (1 := Hstep2), Rmin_l.
rewrite /SF_lx /seq_step /= in Hstep |- * ; move: (Rle_lt_trans _ _ _ (Rmax_r _ _) Hstep) (Rle_lt_trans _ _ _ (Rmax_l _ _) Hstep) => {Hstep} /= H H0.
apply Rmax_case.
by [].
by apply IH.
assert (pointed_subdiv y1 /\ SF_h y1 = SF_h y /\ last (SF_h y1) (unzip1 (SF_t y1)) = last (SF_h y2) (unzip1 (SF_t y2))).
split.
unfold y1 ; move: Hptd Hh2.
clear -Hptd2.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hptd Hl.
rewrite -Hl ; by apply Hptd2.
case => [ | i] /= Hi.
by apply (Hptd O (lt_O_Sn _)).
apply (IH (ptd_cons _ _ Hptd) Hl i (lt_S_n _ _ Hi)).
unfold y1 ; simpl ; split.
by [].
move: Hh2 ; clear ; apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
by rewrite Hl.
by apply IH.
specialize (H1 y1 H H0).
move: Hab Hbc Hh2 H1 H2 ; clear ; set c := last (SF_h y2) (unzip1 (SF_t y2)) ; set b := last (SF_h y) (unzip1 (SF_t y)) ; set a := SF_h y => Hab Hbc Hl.
rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 3!scal_one.
replace (Riemann_sum f y) with (minus (Riemann_sum f y1) (Riemann_sum f y2)).
move => H1 H2.
unfold ball_norm.
set v := minus _ _.
replace v with (minus (minus (Riemann_sum f y1) l1) (minus (Riemann_sum f y2) l2)).
rewrite (double_var eps).
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
rewrite -(norm_opp (minus (Riemann_sum f y2) l2)).
by apply @norm_triangle.
rewrite /v /minus 2!opp_plus opp_opp 2!plus_assoc.
apply (f_equal (fun x => plus x _)).
rewrite -!plus_assoc.
apply f_equal.
by apply plus_comm.
move: Hl ; unfold y1, b.
clear.
apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
by rewrite -Hl /minus plus_opp_r.
rewrite (Riemann_sum_cons _ (x0,y0) {| SF_h := SF_h y; SF_t := SF_t y ++ SF_t y2 |}) /=.
rewrite Riemann_sum_cons /=.
rewrite /minus -plus_assoc.
apply f_equal.
by apply IH.
