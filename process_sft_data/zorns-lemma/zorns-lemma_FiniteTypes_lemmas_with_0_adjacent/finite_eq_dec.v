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

Lemma finite_eq_dec: forall X:Type, FiniteT X -> forall x y:X, {x=y} + {x<>y}.
Proof.
intros.
apply decidable_dec.
induction H.
destruct x.
decide equality.
destruct H0.
case (IHFiniteT (g x) (g y)).
left.
rewrite <- H1.
rewrite <- H1 with x.
rewrite H2.
reflexivity.
right.
contradict H2.
rewrite H2.
reflexivity.
