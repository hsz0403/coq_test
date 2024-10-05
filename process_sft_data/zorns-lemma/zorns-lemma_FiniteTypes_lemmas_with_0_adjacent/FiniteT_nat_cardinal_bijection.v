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

Lemma FiniteT_nat_cardinal_bijection: forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g), FiniteT_nat_cardinal Y (bij_finite X Y g H Hinv) = FiniteT_nat_cardinal X H.
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
apply invertible_impl_bijective in Hinv.
destruct Hinv as [g_inj g_surj].
assert (Full_set = Im Full_set g).
apply Extensionality_Ensembles; split; red; intros; try constructor.
destruct (g_surj x).
exists x0; try constructor; auto.
rewrite H0; apply injection_preserves_cardinal; trivial.
apply FiniteT_nat_cardinal_def.
