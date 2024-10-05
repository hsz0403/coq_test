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

Lemma inj_finite: forall (X Y:Type) (f:X->Y), FiniteT Y -> injective f -> (forall y:Y, (exists x:X, f x = y) \/ (~ exists x:X, f x = y)) -> FiniteT X.
Proof.
intros.
assert (forall y:{y:Y | exists x:X, f x = y}, {x:X | f x = proj1_sig y}).
intro.
destruct y.
simpl.
apply constructive_definite_description.
destruct e.
exists x0.
red; split.
assumption.
intros.
apply H0.
transitivity x.
assumption.
symmetry; assumption.
pose (g := fun y:{y:Y | exists x:X, f x = y} => proj1_sig (X0 y)).
apply bij_finite with _ g.
apply finite_subtype.
assumption.
assumption.
pose (ginv := fun (x:X) => exist (fun y:Y => exists x:X, f x = y) (f x) (ex_intro _ x (refl_equal _))).
exists ginv.
destruct x as [y [x e]].
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
unfold ginv; simpl.
simpl in e0.
repeat match goal with |- context [ex_intro ?f ?x ?e] => generalize (ex_intro f x e) end.
rewrite <- e0.
intros; destruct (proof_irrelevance _ e1 e2).
reflexivity.
intro; unfold ginv.
unfold g; simpl.
match goal with |- context [X0 ?arg] => destruct (X0 arg) end.
simpl.
simpl in e.
auto.
