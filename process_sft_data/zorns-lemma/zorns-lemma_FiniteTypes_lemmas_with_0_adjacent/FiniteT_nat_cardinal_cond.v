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

Lemma FiniteT_nat_cardinal_cond: forall (X:Type) (H:FiniteT X) (n:nat), cardinal _ (@Full_set X) n -> FiniteT_nat_cardinal X H = n.
Proof.
intros.
pose proof (FiniteT_has_nat_cardinal X H).
destruct H1.
red in H1.
destruct H1.
transitivity x.
symmetry; apply H2.
apply FiniteT_nat_cardinal_def.
apply H2; trivial.
