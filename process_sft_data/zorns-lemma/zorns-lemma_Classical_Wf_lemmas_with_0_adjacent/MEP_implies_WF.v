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

Lemma MEP_implies_WF: minimal_element_property -> well_founded R.
Proof.
unfold well_founded.
unfold minimal_element_property.
intro MEP.
apply NNPP.
intuition.
apply not_all_ex_not in H.
destruct H.
assert (Inhabited [x:T | ~ Acc R x]).
exists x.
constructor; assumption.
apply MEP in H0.
destruct H0.
destruct H0.
destruct H0.
contradict H0.
constructor.
intros.
apply NNPP.
intuition.
apply H1 with y.
constructor; assumption.
assumption.
