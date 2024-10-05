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

Lemma continuous_RInt_2 (f : R -> V) (a b : R) (If : R -> V) : locally a (fun z : R => is_RInt f z b (If z)) -> continuous If a.
Proof.
intros.
generalize (locally_singleton _ _ H) => /= Hab.
apply continuous_ext with (fun z => opp (plus (opp (If a)) (minus (If a) (If z)))) ; simpl.
intros x.
by rewrite /minus plus_assoc plus_opp_l plus_zero_l opp_opp.
apply continuous_opp.
apply continuous_plus.
apply filterlim_const.
apply (continuous_RInt_0 f _ (fun x : R_UniformSpace => minus (If a) (If x))).
apply: filter_imp H => x Hx.
eapply is_RInt_Chasles.
by apply Hab.
by apply is_RInt_swap.
