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

Lemma WF_implies_DSP: well_founded R -> decreasing_sequence_property.
Proof.
unfold decreasing_sequence_property.
intros WF a.
remember (a 0) as a0.
revert a0 a Heqa0.
apply (well_founded_ind WF (fun x:T => forall a:nat->T, x = a 0 -> exists n:nat, ~ R (a (S n)) (a n))).
intros.
case (classic (R (a 1) (a 0))).
intro.
pose (b := fun n:nat => a (S n)).
assert (exists n:nat, ~ R (b (S n)) (b n)).
apply H with (a 1).
rewrite H0.
assumption.
trivial.
destruct H2.
exists (S x0).
unfold b in H2.
assumption.
exists 0.
assumption.
