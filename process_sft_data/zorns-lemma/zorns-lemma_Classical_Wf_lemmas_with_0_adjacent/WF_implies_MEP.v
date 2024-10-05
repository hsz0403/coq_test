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

Lemma WF_implies_MEP: well_founded R -> minimal_element_property.
Proof.
unfold well_founded.
unfold minimal_element_property.
intros WF S Hinh.
destruct Hinh.
revert x H.
apply (@well_founded_ind T R WF (fun x:T => In S x -> exists y:T, In S y /\ (forall z:T, In S z -> ~ R z y))).
intros.
case (classic (forall y:T, In S y -> ~ R y x)).
exists x.
split.
assumption.
assumption.
intro.
apply not_all_ex_not in H1.
destruct H1.
apply imply_to_and in H1.
destruct H1.
apply H with x0.
apply NNPP.
assumption.
assumption.
