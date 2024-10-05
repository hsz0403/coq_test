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

Lemma RInt_fct_extend_pair (U_RInt : (R -> U) -> R -> R -> U) (V_RInt : (R -> V) -> R -> R -> V) : (forall f a b l, is_RInt f a b l -> U_RInt f a b = l) -> (forall f a b l, is_RInt f a b l -> V_RInt f a b = l) -> forall f a b l, is_RInt f a b l -> (U_RInt (fun t => fst (f t)) a b, V_RInt (fun t => snd (f t)) a b) = l.
Proof.
intros HU HV f a b l Hf.
apply injective_projections ; simpl.
apply HU ; by apply is_RInt_fct_extend_fst.
apply HV ; by apply is_RInt_fct_extend_snd.
