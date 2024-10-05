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

Lemma RInt_comp (f : R -> V) (g dg : R -> R) (a b : R) : (forall x, Rmin a b <= x <= Rmax a b -> continuous f (g x)) -> (forall x, Rmin a b <= x <= Rmax a b -> is_derive g x (dg x) /\ continuous dg x) -> RInt (fun y => scal (dg y) (f (g y))) a b = RInt f (g a) (g b).
Proof.
move => Hfg Hg.
have H := (is_RInt_comp _ _ _ _ _ Hfg Hg).
exact: is_RInt_unique.
