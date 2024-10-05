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

Lemma RInt_Chasles_bound_comp_l_loc (f : R -> R -> R) (a : R -> R) (b x : R) : locally x (fun y => ex_RInt (f y) (a x) b) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) -> continuous a x -> locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) b = RInt (f x') (a x') b).
Proof.
intros Hab (eps,Hae) Ca.
generalize (proj1 (filterlim_locally _ _) Ca) => {Ca} Ca.
generalize (filter_and _ _ (Ca eps) (filter_and _ _ Hab Hae)).
apply filter_imp => {Ca Hae Hab} y [Hy [Hab Hae]].
apply RInt_Chasles with (2 := Hab).
apply ex_RInt_inside with (1 := Hae).
now apply Rlt_le.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
