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

Lemma is_RInt_ext : forall (f g : R -> V) (a b : R) (l : V), (forall x, Rmin a b < x < Rmax a b -> f x = g x) -> is_RInt f a b l -> is_RInt g a b l.
Proof.
intros f g a b.
wlog: a b / (a < b) => [Hw | Hab] l Heq Hf.
case: (Rle_lt_dec a b) => Hab.
case: Hab => Hab.
by apply Hw.
rewrite -Hab in Hf |- *.
move: Hf ; apply filterlim_ext => x.
by rewrite Rminus_eq_0 sign_0 !scal_zero_l.
rewrite -(opp_opp l).
apply is_RInt_swap.
apply Hw.
by [].
by rewrite Rmin_comm Rmax_comm.
by apply is_RInt_swap.
move: Heq ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Heq.
apply filterlim_locally_ball_norm => eps.
destruct (proj1 (filterlim_locally_ball_norm _ _) Hf (pos_div_2 eps)) as [d Hd].
set dx := fun x => pos_div_2 (pos_div_2 eps) / Rmax 1 (norm (minus (g x) (f x))).
assert (forall x, 0 < dx x).
intros x.
apply Rdiv_lt_0_compat.
apply is_pos_div_2.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
assert (Hdelta : 0 < Rmin d (Rmin (dx a) (dx b))).
repeat apply Rmin_case => //.
by apply d.
exists (mkposreal _ Hdelta) => /= y Hstep [Hptd [Hya Hyb]].
rewrite (double_var eps).
eapply ball_norm_triangle.
apply Hd.
eapply Rlt_le_trans, Rmin_l.
by apply Hstep.
split => //.
have: (seq_step (SF_lx y) < (Rmin (dx a) (dx b))) => [ | {Hstep} Hstep].
eapply Rlt_le_trans, Rmin_r.
by apply Hstep.
clear d Hd Hdelta Hf.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite !scal_one.
move: Hya Hyb ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Hya Hyb.
move: Hab Heq Hstep ; rewrite -Hyb => {b Hyb} ; set b := last (SF_h y) (unzip1 (SF_t y)) ; rewrite -Hya => {a Hya} ; set a := SF_h y => Hab Heq Hstep.
revert a b Hab Heq Hptd Hstep ; apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IH] a b Hab Heq Hptd Hstep.
rewrite !Riemann_sum_zero //.
by apply (ball_norm_center _ (pos_div_2 eps)).
rewrite !Riemann_sum_cons.
assert (Hx0 := proj1 (ptd_sort _ Hptd)).
case: Hx0 => /= Hx0.
Focus 2.
rewrite Hx0 Rminus_eq_0 !scal_zero_l !plus_zero_l.
apply: IH.
move: Hab ; unfold a, b ; simpl ; by rewrite Hx0.
intros x Hx.
apply Heq ; split.
unfold a ; simpl ; rewrite Hx0 ; apply Hx.
unfold b ; simpl ; apply Hx.
eapply ptd_cons, Hptd.
move: Hstep ; unfold a, b ; simpl ; rewrite Hx0.
apply Rle_lt_trans, Rmax_r.
clear IH.
rewrite (double_var (eps / 2)).
eapply Rle_lt_trans, Rplus_lt_compat.
eapply Rle_trans, norm_triangle.
apply Req_le, f_equal.
replace (@minus V _ _) with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0)))) (minus (Riemann_sum g y) (Riemann_sum f y))).
by [].
rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
apply f_equal.
rewrite !plus_assoc ; apply f_equal2 => //.
by apply plus_comm.
eapply Rle_lt_trans.
apply @norm_scal.
assert (Ha := proj1 (Hptd O (lt_O_Sn _))).
case: Ha => /= Ha.
assert (Hb : snd x0 <= b).
eapply Rle_trans, sorted_last.
2: apply ptd_sort.
2: eapply ptd_cons, Hptd.
2: apply lt_O_Sn.
simpl.
apply (Hptd O), lt_O_Sn.
case: Hb => //= Hb.
rewrite Heq.
rewrite minus_eq_zero norm_zero Rmult_0_r.
apply (is_pos_div_2 (pos_div_2 eps)).
by split.
rewrite Hb.
eapply Rle_lt_trans.
apply Rmult_le_compat_l, (Rmax_r 1).
by apply abs_ge_0.
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
rewrite -/(dx b).
eapply Rlt_le_trans, Rmin_r.
eapply Rle_lt_trans, Hstep.
by apply Rmax_l.
rewrite -Ha.
eapply Rle_lt_trans.
apply Rmult_le_compat_l, (Rmax_r 1).
by apply abs_ge_0.
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
rewrite -/(dx a).
eapply Rlt_le_trans, Rmin_l.
eapply Rle_lt_trans, Hstep.
by apply Rmax_l.
have: (forall x : R, SF_h y <= x < b -> f x = g x) => [ | {Heq} Heq].
intros.
apply Heq ; split.
by eapply Rlt_le_trans, H0.
by apply H0.
have: (seq_step (SF_lx y) < (dx b)) => [ | {Hstep} Hstep].
eapply Rlt_le_trans, Rmin_r.
eapply Rle_lt_trans, Hstep.
apply Rmax_r.
simpl in b.
apply ptd_cons in Hptd.
clear a Hab x0 Hx0.
revert b Heq Hptd Hstep ; apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IH] b Heq Hptd Hstep.
rewrite !Riemann_sum_zero // minus_eq_zero norm_zero.
apply (is_pos_div_2 (pos_div_2 _)).
rewrite !Riemann_sum_cons.
replace (minus (plus (scal (SF_h y - fst x0) (g (snd x0))) (Riemann_sum g y)) (plus (scal (SF_h y - fst x0) (f (snd x0))) (Riemann_sum f y))) with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0)))) (minus (Riemann_sum g y) (Riemann_sum f y))).
eapply Rle_lt_trans.
apply @norm_triangle.
assert (SF_h y <= b).
eapply Rle_trans, sorted_last.
2: apply ptd_sort ; eapply ptd_cons, Hptd.
2: apply lt_O_Sn.
simpl ; by apply Rle_refl.
case: H0 => Hb.
rewrite Heq.
rewrite minus_eq_zero scal_zero_r norm_zero Rplus_0_l.
apply IH ; intros.
apply Heq ; split.
eapply Rle_trans, H0.
eapply Rle_trans ; by apply (Hptd O (lt_O_Sn _)).
by apply H0.
eapply ptd_cons, Hptd.
eapply Rle_lt_trans, Hstep.
by apply Rmax_r.
split.
apply (Hptd O (lt_O_Sn _)).
eapply Rle_lt_trans, Hb.
apply (Hptd O (lt_O_Sn _)).
clear IH.
rewrite Hb !Riemann_sum_zero //.
rewrite minus_eq_zero norm_zero Rplus_0_r.
eapply Rle_lt_trans.
apply @norm_scal.
assert (snd x0 <= b).
rewrite -Hb.
apply (Hptd O (lt_O_Sn _)).
case: H0 => Hb'.
rewrite Heq.
rewrite minus_eq_zero norm_zero Rmult_0_r.
apply (is_pos_div_2 (pos_div_2 _)).
split.
apply (Hptd O (lt_O_Sn _)).
by [].
rewrite Hb'.
eapply Rle_lt_trans.
apply Rmult_le_compat_l.
apply abs_ge_0.
apply (Rmax_r 1).
apply Rlt_div_r.
eapply Rlt_le_trans, Rmax_l.
by apply Rlt_0_1.
eapply Rle_lt_trans, Hstep.
rewrite -Hb.
by apply Rmax_l.
apply ptd_sort ; eapply ptd_cons, Hptd.
apply ptd_sort ; eapply ptd_cons, Hptd.
rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
apply f_equal.
rewrite !plus_assoc.
apply f_equal2 => //.
by apply plus_comm.
