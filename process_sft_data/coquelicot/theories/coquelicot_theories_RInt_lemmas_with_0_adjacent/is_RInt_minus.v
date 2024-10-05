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

Lemma is_RInt_minus : forall (f g : R -> V) (a b : R) (If Ig : V), is_RInt f a b If -> is_RInt g a b Ig -> is_RInt (fun y => minus (f y) (g y)) a b (minus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (opp 1) (scal (sign (b - a)) (Riemann_sum g ptd))))).
intros ptd.
rewrite Riemann_sum_minus.
unfold minus.
rewrite scal_opp_one.
rewrite -scal_opp_r.
apply sym_eq, @scal_distr_l.
eapply filterlim_comp_2 with (1 := Hf).
apply filterlim_comp with (1 := Hg).
eapply @filterlim_scal_r.
rewrite scal_opp_one.
apply: filterlim_plus.
