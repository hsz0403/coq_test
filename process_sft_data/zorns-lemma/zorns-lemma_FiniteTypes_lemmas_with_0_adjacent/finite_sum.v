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

Lemma finite_sum: forall X Y:Type, FiniteT X -> FiniteT Y -> FiniteT (X+Y).
Proof.
intros.
induction H0.
apply bij_finite with _ inl.
assumption.
pose (g := fun (x:X+False) => match x with | inl x => x | inr f => False_rect X f end).
exists g.
intro; simpl.
reflexivity.
destruct y.
simpl.
reflexivity.
destruct f.
pose (g := fun (x:option (X+T)) => match x with | Some (inl x) => inl _ x | Some (inr t) => inr _ (Some t) | None => inr _ None end).
apply bij_finite with _ g.
apply add_finite.
assumption.
pose (ginv := fun (x:X + option T) => match x with | inl x => Some (inl _ x) | inr (Some t) => Some (inr _ t) | inr None => None end).
exists ginv.
destruct x as [[x|t]|]; trivial.
destruct y as [x|[t|]]; trivial.
pose (g := fun (x:X+X0) => match x with | inl x0 => inl _ x0 | inr x0 => inr _ (f x0) end).
destruct H1.
pose (ginv := fun (x:X+Y) => match x with | inl x0 => inl _ x0 | inr y0 => inr _ (g0 y0) end).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x0|x0]; trivial.
simpl.
rewrite H1; reflexivity.
destruct y as [x|y0]; trivial.
simpl.
rewrite H2; reflexivity.
