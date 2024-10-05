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

Lemma surj_finite: forall (X Y:Type) (f:X->Y), FiniteT X -> surjective f -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) -> FiniteT Y.
Proof.
intros.
apply bij_finite with {y:Y | In (Im Full_set f) y} (@proj1_sig _ (fun y:Y => In (Im Full_set f) y)).
apply Finite_ens_type.
apply FiniteT_img.
assumption.
assumption.
assert (forall y:Y, In (Im Full_set f) y).
intro.
destruct (H0 y).
exists x; auto with sets.
constructor.
pose (proj1_sig_inv := fun y:Y => exist (fun y0:Y => In (Im Full_set f) y0) y (H2 y)).
exists proj1_sig_inv.
destruct x.
simpl.
unfold proj1_sig_inv.
destruct (proof_irrelevance _ (H2 x) i); trivial.
intros; simpl; reflexivity.
