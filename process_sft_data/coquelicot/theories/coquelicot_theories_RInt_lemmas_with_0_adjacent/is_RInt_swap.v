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

Lemma is_RInt_swap : forall (f : R -> V) (a b : R) (If : V), is_RInt f b a If -> is_RInt f a b (opp If).
Proof.
unfold is_RInt.
intros f a b If HIf.
rewrite -scal_opp_one /=.
apply filterlim_ext with (fun ptd => scal (opp (one : R)) (scal (sign (a - b)) (Riemann_sum f ptd))).
intros x.
rewrite scal_assoc.
apply (f_equal (fun s => scal s _)).
rewrite /mult /opp /one /=.
by rewrite -(Ropp_minus_distr' b a) sign_opp /= Ropp_mult_distr_l_reverse Rmult_1_l.
unfold Riemann_fine.
rewrite Rmin_comm Rmax_comm.
apply filterlim_comp with (1 := HIf).
apply: filterlim_scal_r.
