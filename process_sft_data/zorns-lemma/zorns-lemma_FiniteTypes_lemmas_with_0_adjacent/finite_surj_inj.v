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

Lemma finite_surj_inj: forall (X:Type) (f:X->X), FiniteT X -> surjective f -> injective f.
Proof.
intros.
assert (exists g:X->X, forall x:X, f (g x) = x).
apply finite_choice with (R:=fun (x y:X) => f y = x).
assumption.
assumption.
destruct H1 as [g].
assert (surjective g).
apply finite_inj_surj.
assumption.
red; intros.
rewrite <- H1 with x.
rewrite <- H1 with y.
rewrite H2; reflexivity.
red; intros.
destruct (H2 x).
destruct (H2 y).
rewrite <- H4 in H3.
rewrite <- H5 in H3.
repeat rewrite H1 in H3.
rewrite <- H4.
rewrite <- H5.
rewrite H3.
reflexivity.
