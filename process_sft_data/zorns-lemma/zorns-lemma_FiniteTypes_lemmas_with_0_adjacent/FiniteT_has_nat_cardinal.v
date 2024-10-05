Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Finite_sets.
Require Export FunctionProperties.
Require Import DecidableDec.
Require Import ProofIrrelevance.
Require Import Description.
Set Asymmetric Patterns.
Inductive FiniteT : Type -> Prop := | empty_finite: FiniteT False | add_finite: forall T:Type, FiniteT T -> FiniteT (option T) | bij_finite: forall (X Y:Type) (f:X->Y), FiniteT X -> invertible f -> FiniteT Y.
Require Import FunctionalExtensionality.
Definition FiniteT_nat_cardinal (X:Type) (H:FiniteT X) : nat := proj1_sig (constructive_definite_description _ (FiniteT_has_nat_cardinal X H)).

Lemma FiniteT_has_nat_cardinal: forall X:Type, FiniteT X -> exists! n:nat, cardinal _ (@Full_set X) n.
Proof.
intros.
apply -> unique_existence; split.
apply finite_cardinal.
pose (idX := fun x:X => x).
assert (Im Full_set idX = Full_set).
apply Extensionality_Ensembles.
red; split.
red; intros; constructor.
red; intros.
exists x.
constructor.
trivial.
rewrite <- H0.
apply FiniteT_img with (f:=fun x:X => x).
assumption.
intros.
case (finite_eq_dec X H y1 y2); tauto.
red; intros.
apply cardinal_unicity with X Full_set; trivial.
