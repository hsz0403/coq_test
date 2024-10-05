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

Lemma RInt_gt_0 (g : R -> R) (a b : R) : (a < b) -> (forall x, a < x < b -> (0 < g x)) -> (forall x, a <= x <= b -> continuous g x) -> 0 < RInt g a b.
Proof.
intros Hab Hg Cg.
set c := (a + b) / 2.
assert (Hc : a < c < b).
unfold c ; lra.
assert (H : locally c (fun (x : R) => g c / 2 <= g x)).
specialize (Hg _ Hc).
specialize (Cg c (conj (Rlt_le _ _ (proj1 Hc)) (Rlt_le _ _ (proj2 Hc)))).
case: (proj1 (filterlim_locally _ _) Cg (pos_div_2 (mkposreal _ Hg))) => /= d Hd.
exists d => /= x Hx.
specialize (Hd _ Hx).
rewrite /ball /= /AbsRing_ball in Hd.
apply Rabs_lt_between' in Hd.
field_simplify (g c - g c / 2) in Hd.
by apply Rlt_le, Hd.
assert (Ig : ex_RInt g a b).
apply @ex_RInt_continuous.
rewrite Rmin_left.
rewrite Rmax_right.
intros.
now apply Cg.
by apply Rlt_le.
by apply Rlt_le.
case: H => /= d Hd.
set a' := Rmax (c - d / 2) ((a + c) / 2).
set b' := Rmin (c + d / 2) ((c + b) / 2).
assert (Hab' : a' < b').
apply Rlt_trans with c.
apply Rmax_case.
generalize (cond_pos d) ; lra.
lra.
apply Rmin_case.
generalize (cond_pos d) ; lra.
lra.
assert (Ha' : a < a' < b).
split.
eapply Rlt_le_trans, Rmax_r.
lra.
apply Rmax_case.
generalize (cond_pos d) ; lra.
lra.
assert (Hb' : a < b' < b).
split.
lra.
eapply Rle_lt_trans.
apply Rmin_r.
lra.
assert (ex_RInt g a a').
eapply @ex_RInt_Chasles_1, Ig ; split ; by apply Rlt_le, Ha'.
assert (ex_RInt g a' b).
eapply @ex_RInt_Chasles_2, Ig ; split ; by apply Rlt_le, Ha'.
assert (ex_RInt g a' b').
eapply @ex_RInt_Chasles_1, H0 ; split => // ; apply Rlt_le => //.
by apply Hb'.
assert (ex_RInt g b' b).
eapply @ex_RInt_Chasles_2, H0 ; split => // ; apply Rlt_le => //.
by apply Hb'.
rewrite -(RInt_Chasles g a a' b) //.
apply Rplus_le_lt_0_compat.
apply (is_RInt_ge_0 g a a').
by apply Rlt_le, Ha'.
exact: RInt_correct.
intros ; apply Rlt_le, Hg ; split.
by apply H3.
eapply Rlt_trans, Ha'.
apply H3.
rewrite -(RInt_Chasles g a' b' b) //.
apply Rplus_lt_le_0_compat.
apply Rlt_le_trans with ((b' - a') * (g c / 2)).
specialize (Hg _ Hc).
apply Rmult_lt_0_compat.
by apply -> Rminus_lt_0.
apply Rdiv_lt_0_compat => //.
by apply Rlt_0_2.
eapply is_RInt_le.
apply Rlt_le, Hab'.
apply @is_RInt_const.
exact: RInt_correct.
intros ; apply Hd.
rewrite (double_var d).
apply Rabs_lt_between' ; split.
eapply Rlt_trans, H3.
eapply Rlt_le_trans, Rmax_l.
apply Rminus_lt_0 ; ring_simplify.
by apply is_pos_div_2.
eapply Rlt_trans.
apply H3.
eapply Rle_lt_trans.
apply Rmin_l.
apply Rminus_lt_0 ; ring_simplify.
by apply is_pos_div_2.
eapply is_RInt_ge_0.
2: exact: RInt_correct.
apply Rlt_le, Hb'.
intros ; apply Rlt_le, Hg.
split.
eapply Rlt_trans, H3.
by apply Hb'.
by apply H3.
