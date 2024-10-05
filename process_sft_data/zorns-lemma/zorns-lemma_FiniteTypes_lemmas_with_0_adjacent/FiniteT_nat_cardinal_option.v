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

Lemma FiniteT_nat_cardinal_option: forall (X:Type) (H:FiniteT X), FiniteT_nat_cardinal (option X) (add_finite X H) = S (FiniteT_nat_cardinal X H).
Proof.
intros.
apply FiniteT_nat_cardinal_cond.
assert (Full_set = Add (Im Full_set (@Some X)) None).
apply Extensionality_Ensembles; split.
red; intros.
destruct x.
left; exists x; constructor.
right; constructor.
red; intros; constructor.
rewrite H0.
constructor.
apply injection_preserves_cardinal.
apply FiniteT_nat_cardinal_def.
red; intros x1 x2 Heq; injection Heq; trivial.
red; intro.
inversion H1.
discriminate H3.
