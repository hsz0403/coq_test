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

Lemma is_RInt_Chasles (f : R -> V) (a b c : R) (l1 l2 : V) : is_RInt f a b l1 -> is_RInt f b c l2 -> is_RInt f a c (plus l1 l2).
Proof.
wlog: a c l1 l2 / (a <= c) => [Hw | Hac].
move => H1 H2.
case: (Rle_lt_dec a c) => Hac.
by apply Hw.
rewrite -(opp_opp (plus _ _)) opp_plus plus_comm.
apply is_RInt_swap.
apply Hw.
by apply Rlt_le.
by apply is_RInt_swap.
by apply is_RInt_swap.
case: (Req_dec a b) => [ <- {b} | Hab'] H1.
-
move => H2.
apply filterlim_locally_ball_norm => /= eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
assert (pointed_subdiv (SF_nil a) /\ SF_h (SF_nil (T := V) a) = Rmin a a /\ last (SF_h (SF_nil (T := V) a)) (unzip1 (SF_t (SF_nil (T := V) a))) = Rmax a a).
split.
move => i Hi ; by apply lt_n_O in Hi.
rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl a).
specialize (H1 (SF_nil a) (cond_pos d1) H) => {H d1}.
rewrite Rminus_eq_0 sign_0 in H1.
assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
rewrite /ball_norm H /minus plus_zero_l in H1 => {H}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
exists d2 => ptd Hstep Hptd.
apply Rle_lt_trans with (norm (minus (scal (sign (c - a)) (Riemann_sum f ptd)) l2) + norm (opp l1)).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite /minus opp_plus -plus_assoc.
by apply f_equal, @plus_comm.
rewrite (double_var eps) ; apply Rplus_lt_compat.
by apply H2.
by apply H1.
case: (Req_dec b c) => [ <- | Hbc'] H2.
-
apply filterlim_locally_ball_norm => /= eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
assert (pointed_subdiv (SF_nil b) /\ SF_h (SF_nil (T := V) b) = Rmin b b /\ last (SF_h (SF_nil (T := V) b)) (unzip1 (SF_t (SF_nil (T := V) b))) = Rmax b b).
split.
move => i Hi ; by apply lt_n_O in Hi.
rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl b).
specialize (H2 (SF_nil b) (cond_pos d2) H) => {H d2}.
rewrite Rminus_eq_0 sign_0 in H2.
assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
rewrite /ball_norm H /minus plus_zero_l in H2 => {H}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
exists d1 => ptd Hstep Hptd.
apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f ptd)) l1) + norm (opp l2)).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
by rewrite /minus opp_plus -plus_assoc.
rewrite (double_var eps) ; apply Rplus_lt_compat.
by apply H1.
by apply H2.
case: (Req_dec a c) => Hac'.
-
rewrite -Hac' in H1 Hbc' H2 Hac |- * => {c Hac'}.
apply is_RInt_swap in H2.
apply filterlim_locally_ball_norm => /= eps.
exists (mkposreal _ Rlt_0_1) => y Hstep Hy.
rewrite Rminus_eq_0 sign_0.
assert (H := scal_zero_l (Riemann_sum f y)).
rewrite /ball_norm H /minus plus_zero_l opp_plus => {H y Hstep Hy}.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\ pointed_subdiv y /\ SF_h y = Rmin a b /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax a b).
apply filter_ex.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
repeat (split => //=).
by apply H5.
by apply H6.
case: H => y [Hstep Hy].
specialize (H1 _ (Rlt_le_trans _ _ _ Hstep (Rmin_l _ _)) Hy).
specialize (H2 _ (Rlt_le_trans _ _ _ Hstep (Rmin_r _ _)) Hy).
rewrite (double_var eps).
rewrite /ball_norm -norm_opp /minus opp_plus opp_opp in H2.
apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
apply Rle_trans with (2 := norm_triangle _ _).
apply Req_le, f_equal.
rewrite plus_assoc /minus.
apply (f_equal (fun x => plus x _)).
by rewrite plus_comm plus_assoc plus_opp_l plus_zero_l.
case: (Rle_lt_dec a b) => Hab ; try (case: Hab => //= Hab) ; clear Hab' ; case: (Rle_lt_dec b c) => Hbc ; try (case: Hbc => //= Hbc) ; clear Hbc' ; try (case: Hac => //= Hac) ; clear Hac'.
by apply is_RInt_Chasles_0 with b.
apply is_RInt_swap in H2.
rewrite -(opp_opp l2).
by apply is_RInt_Chasles_1 with b.
apply is_RInt_swap in H1.
rewrite -(opp_opp l1) plus_comm.
by apply is_RInt_Chasles_2 with b.
now contradict Hab ; apply Rle_not_lt, Rlt_le, Rlt_trans with c.
