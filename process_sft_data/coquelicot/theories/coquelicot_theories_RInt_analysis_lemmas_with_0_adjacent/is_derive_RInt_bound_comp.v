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

Lemma is_derive_RInt_bound_comp (f : R -> V) (If : R -> R -> V) (a b : R -> R) (da db x : R) : locally (a x, b x) (fun u : R * R => is_RInt f (fst u) (snd u) (If (fst u) (snd u))) -> continuous f (a x) -> continuous f (b x) -> is_derive a x da -> is_derive b x db -> is_derive (fun x => If (a x) (b x)) x (minus (scal db (f (b x))) (scal da (f (a x)))).
Proof.
intros Iab Ca Cb Da Db.
unfold is_derive.
eapply filterdiff_ext_lin.
apply @filterdiff_comp'_2.
apply Da.
apply Db.
eapply filterdiff_ext_lin.
apply (filterdiff_RInt f If (a x) (b x)).
exact Iab.
exact Ca.
exact Cb.
by case => y z /=.
simpl => y.
by rewrite -!scal_assoc scal_minus_distr_l.
