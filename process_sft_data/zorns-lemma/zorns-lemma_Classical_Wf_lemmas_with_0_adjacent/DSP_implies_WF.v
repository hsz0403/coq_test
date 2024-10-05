Require Import Classical.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import EnsemblesSpec.
Section MinimalElements.
Variable T:Type.
Variable R:relation T.
Definition minimal_element_property : Prop := forall S:Ensemble T, Inhabited S -> exists x:T, In S x /\ forall y:T, In S y -> ~ R y x.
End MinimalElements.
Require Import ClassicalChoice.
Section DecreasingSequences.
Variable T:Type.
Variable R:relation T.
Definition decreasing_sequence_property := forall a:nat->T, exists n:nat, ~ R (a (S n)) (a n).
End DecreasingSequences.

Lemma DSP_implies_WF: decreasing_sequence_property -> well_founded R.
Proof.
unfold decreasing_sequence_property.
intro DSP.
apply MEP_implies_WF.
unfold minimal_element_property.
intro S0.
intros.
apply NNPP.
intuition.
assert (forall x:T, In S0 x -> exists y:T, In S0 y /\ R y x).
intros.
apply NNPP.
intuition.
assert (forall y:T, ~(In S0 y /\ R y x)).
apply not_ex_all_not.
assumption.
apply H0.
exists x.
split.
assumption.
intros.
apply H3 with y.
tauto.
pose (S_type := {x:T | In S0 x}).
assert (exists f:S_type -> S_type, forall x:S_type, R (proj1_sig (f x)) (proj1_sig x)).
apply choice with (R:=fun x y:S_type => R (proj1_sig y) (proj1_sig x)).
intro.
destruct x.
simpl.
pose proof (H1 x i).
destruct H2.
destruct H2.
exists (exist (fun x:T => In S0 x) x0 H2).
simpl.
assumption.
destruct H2 as [f Hf].
destruct H.
pose (b := nat_rect (fun n:nat => S_type) (exist (fun x:T => In S0 x) x H) (fun (n:nat) (x:S_type) => f x)).
simpl in b.
pose (a := fun n:nat => (proj1_sig (b n))).
assert (forall n:nat, R (a (S n)) (a n)).
unfold a.
intro.
simpl.
apply Hf.
contradict DSP.
apply ex_not_not_all.
exists a.
apply all_not_not_ex.
auto.
