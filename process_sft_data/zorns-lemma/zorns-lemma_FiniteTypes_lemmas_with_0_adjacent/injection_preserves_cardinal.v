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

Lemma injection_preserves_cardinal: forall (X Y:Type) (f:X->Y) (n:nat) (S:Ensemble X), cardinal _ S n -> injective f -> cardinal _ (Im S f) n.
Proof.
intros.
induction H.
assert (Im Empty_set f = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H.
destruct H.
rewrite H; constructor.
assert (Im (Add A x) f = Add (Im A f) (f x)).
apply Extensionality_Ensembles; split.
red; intros.
destruct H2.
symmetry in H3; destruct H3.
destruct H2.
left; exists x0; auto with sets.
destruct H2; right; auto with sets.
red; intros.
destruct H2.
destruct H2.
exists x0.
left; auto with sets.
assumption.
destruct H2.
exists x; trivial; right; auto with sets.
rewrite H2.
constructor; trivial.
red; intro H3; inversion H3.
apply H0 in H5; destruct H5.
contradiction H1.
