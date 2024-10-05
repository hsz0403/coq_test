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

Lemma norm_RInt_le : forall (f : R -> V) (g : R -> R) (a b : R) (lf : V) (lg : R), a <= b -> (forall x, a <= x <= b -> norm (f x) <= g x) -> is_RInt f a b lf -> is_RInt g a b lg -> norm lf <= lg.
Proof.
intros f g a b lf lg Hab H Hf Hg.
change (Rbar_le (norm lf) lg).
apply (filterlim_le (F := Riemann_fine a b)) with (fun ptd : SF_seq => norm (scal (sign (b - a)) (Riemann_sum f ptd))) (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum g ptd)).
3: apply Hg.
exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
destruct Hab as [Hab|Hab].
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite !scal_one.
apply Riemann_sum_norm.
by [].
move => t.
rewrite Hl Hh /Rmin /Rmax ; case: Rle_dec => [_|].
apply H.
move => /Rnot_le_lt Hab'.
elim (Rlt_not_le _ _ Hab).
now apply Rlt_le.
rewrite -> Rminus_diag_eq by now apply sym_eq.
rewrite sign_0.
rewrite 2!scal_zero_l.
rewrite norm_zero ; by right.
apply filterlim_comp with (locally lf).
by apply Hf.
by apply filterlim_norm.
