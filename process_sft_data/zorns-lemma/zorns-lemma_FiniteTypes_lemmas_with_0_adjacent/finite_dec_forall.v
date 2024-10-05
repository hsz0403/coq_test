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

Lemma finite_dec_forall: forall (X:Type) (P:X->Prop), FiniteT X -> (forall x:X, { P x } + { ~ P x }) -> { forall x:X, P x } + { exists x:X, ~ P x }.
Proof.
intros.
apply exclusive_dec.
intuition.
destruct H2.
contradiction (H1 x).
revert P X0.
induction H.
left.
destruct x.
intros.
case (IHFiniteT (fun x:T => P (Some x)) (fun x:T => X0 (Some x))).
intro.
case (X0 None).
left.
destruct x.
apply H0.
assumption.
right.
exists None.
assumption.
right.
destruct H0.
exists (Some x).
assumption.
intros.
destruct H0.
case (IHFiniteT (fun x:X => P (f x)) (fun x:X => X0 (f x))).
left.
intro y.
rewrite <- H1.
apply H2.
right.
destruct H2.
exists (f x).
assumption.
