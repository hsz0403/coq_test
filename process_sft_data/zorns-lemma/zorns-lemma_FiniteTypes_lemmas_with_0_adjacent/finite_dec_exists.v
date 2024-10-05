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

Lemma finite_dec_exists: forall (X:Type) (P:X->Prop), FiniteT X -> (forall x:X, {P x} + {~ P x}) -> { exists x:X, P x } + { forall x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
red; intro.
destruct H0.
destruct H0.
contradiction (H1 x).
revert P X0.
induction H.
right.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x)) (fun x:T => X0 (Some x))).
left.
destruct H0.
exists (Some x).
assumption.
intro.
case (X0 None).
left.
exists None.
assumption.
right.
destruct x.
apply H0.
assumption.
destruct H0.
intros.
case (IHFiniteT (fun x:X => P (f x)) (fun x:X => X0 (f x))).
left.
destruct H2.
exists (f x).
assumption.
right.
intro.
rewrite <- H1 with x.
apply H2.
