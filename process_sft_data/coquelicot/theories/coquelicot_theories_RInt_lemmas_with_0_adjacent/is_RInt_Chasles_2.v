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

Lemma is_RInt_Chasles_2 (f : R -> V) (a b c : R) l1 l2 : a < b < c -> is_RInt f a c l1 -> is_RInt f a b l2 -> is_RInt f b c (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
rewrite -(Ropp_involutive a) -(Ropp_involutive b) -(Ropp_involutive c) in H1 H2.
apply is_RInt_comp_opp, is_RInt_swap in H1.
apply is_RInt_comp_opp, is_RInt_swap in H2.
apply Ropp_lt_contravar in Hab.
apply Ropp_lt_contravar in Hbc.
generalize (is_RInt_Chasles_1 _ _ _ _ _ _ (conj Hbc Hab) H1 H2).
clear => H.
apply is_RInt_comp_opp, is_RInt_swap in H.
replace (minus l1 l2) with (opp (minus (opp l1) (opp l2))).
move: H ; apply is_RInt_ext.
now move => x _ ; rewrite opp_opp Ropp_involutive.
by rewrite /minus opp_plus 2!opp_opp.
