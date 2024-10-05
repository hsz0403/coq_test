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

Lemma ex_RInt_Chasles_0 (f : R -> V) (a b c : R) : a <= b <= c -> ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
case => Hab Hbc H1 H2.
case: Hab => [ Hab | -> ] //.
case: Hbc => [ Hbc | <- ] //.
case: H1 => [l1 H1] ; case: H2 => [l2 H2].
exists (plus l1 l2).
apply is_RInt_Chasles_0 with b ; try assumption.
by split.
