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

Lemma finite_inj_surj: forall (X:Type) (f:X->X), FiniteT X -> injective f -> surjective f.
Proof.
intros.
induction H.
red.
destruct y.
remember (f None) as f0; destruct f0 as [a|].
assert (forall x:T, f (Some x) <> Some a).
unfold not; intros.
assert (Some x = None).
apply H0.
congruence.
discriminate H2.
pose (g := fun x:T => match f (Some x) with | Some y => y | None => a end).
assert (surjective g).
apply IHFiniteT.
red; intros.
remember (f (Some x)) as fx; destruct fx; remember (f (Some y)) as fy; destruct fy.
unfold g in H2.
rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2; assert (f (Some x) = f (Some y)).
congruence.
apply H0 in H2.
injection H2; trivial.
unfold g in H2; rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2.
contradiction (H1 x).
symmetry; assumption.
unfold g in H2; rewrite <- Heqfx in H2; rewrite <- Heqfy in H2.
destruct H2.
contradiction (H1 y).
symmetry; assumption.
assert (Some x = Some y).
apply H0.
congruence.
injection H3; trivial.
red; intro.
destruct y.
case (finite_eq_dec _ H t a).
exists None.
congruence.
destruct (H2 t).
exists (Some x).
unfold g in H3.
destruct (f (Some x)).
congruence.
contradiction n.
symmetry; assumption.
destruct (H2 a).
exists (Some x).
unfold g in H3.
remember (f (Some x)) as fx; destruct fx.
destruct H3.
contradiction (H1 x).
symmetry; assumption.
reflexivity.
assert (forall x:T, { y:T | f (Some x) = Some y }).
intros.
remember (f (Some x)) as fx; destruct fx.
exists t; reflexivity.
assert (Some x = None).
apply H0.
congruence.
discriminate H1.
pose (g := fun x:T => proj1_sig (X x)).
assert (surjective g).
apply IHFiniteT.
red; intros.
unfold g in H1.
repeat destruct X in H1.
simpl in H1.
assert (Some x = Some y).
apply H0.
congruence.
injection H2; trivial.
red; intro.
destruct y.
destruct (H1 t).
unfold g in H2; destruct X in H2.
simpl in H2.
exists (Some x).
congruence.
exists None.
symmetry; assumption.
destruct H1.
pose (f' := fun (x:X) => g (f (f0 x))).
assert (surjective f').
apply IHFiniteT.
red; intros.
unfold f' in H3.
assert (f (f0 x) = f (f0 y)).
congruence.
apply H0 in H4.
congruence.
red; intro.
destruct (H3 (g y)).
unfold f' in H4.
exists (f0 x).
congruence.
