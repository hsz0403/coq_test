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

Lemma finite_prod: forall (X Y:Type), FiniteT X -> FiniteT Y -> FiniteT (X*Y).
Proof.
intros.
induction H0.
apply bij_finite with _ (False_rect _).
constructor.
exists (@snd X False).
destruct x.
destruct y.
destruct f.
pose (g := fun (x:X*T + X) => match x with | inl (pair x0 t) => pair x0 (Some t) | inr x0 => pair x0 None end).
pose (ginv := fun (x:X * option T) => match x with | (x0, Some t) => inl _ (x0, t) | (x0, None) => inr _ x0 end).
apply bij_finite with _ g.
apply finite_sum.
assumption.
assumption.
exists ginv.
destruct x as [[x0 t]|x0]; trivial.
destruct y as [x0 [t|]]; trivial.
pose (g := fun (y:X*X0) => match y with | pair x x0 => pair x (f x0) end).
destruct H1.
pose (ginv := fun (y:X*Y) => let (x,y0) := y in (x, g0 y0)).
apply bij_finite with _ g.
assumption.
exists ginv.
destruct x as [x x0]; unfold ginv, g; try rewrite H1; trivial.
destruct y as [x y]; unfold ginv, g; try rewrite H2; trivial.
