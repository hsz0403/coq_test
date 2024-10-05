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

Lemma RInt_Chasles_bound_comp_loc (f : R -> R -> R) (a b : R -> R) (x : R) : locally x (fun y => ex_RInt (f y) (a x) (b x)) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (a x - eps) (a x + eps))) -> (exists eps : posreal, locally x (fun y => ex_RInt (f y) (b x - eps) (b x + eps))) -> continuous a x -> continuous b x -> locally x (fun x' => RInt (f x') (a x') (a x) + RInt (f x') (a x) (b x') = RInt (f x') (a x') (b x')).
Proof.
intros Hab (ea,Hae) (eb,Hbe) Ca Cb.
generalize (proj1 (filterlim_locally _ _) Ca) => {Ca} Ca.
generalize (proj1 (filterlim_locally _ _) Cb) => {Cb} Cb.
set (e := mkposreal _ (Rmin_stable_in_posreal ea eb)).
generalize (filter_and _ _ (filter_and _ _ (Ca e) (Cb e)) (filter_and _ _ Hab (filter_and _ _ Hae Hbe))).
apply filter_imp => {Ca Cb Hab Hae Hbe} y [[Hay Hby] [Hab [Hae Hbe]]].
apply: RInt_Chasles.
apply ex_RInt_inside with (1 := Hae).
apply Rlt_le.
apply Rlt_le_trans with (1 := Hay).
exact: Rmin_l.
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply ex_RInt_Chasles with (1 := Hab).
apply ex_RInt_inside with (1 := Hbe).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply Rlt_le, cond_pos.
apply Rlt_le.
apply Rlt_le_trans with (1 := Hby).
exact: Rmin_r.
