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

Lemma FiniteT_img: forall (X Y:Type) (f:X->Y), FiniteT X -> (forall y1 y2:Y, y1=y2 \/ y1<>y2) -> Finite _ (Im Full_set f).
Proof.
intros.
induction H.
assert (Im Full_set f = Empty_set).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H.
destruct x.
auto with sets.
rewrite H.
constructor.
assert ({exists x:T, f (Some x) = f None} + {forall x:T, f (Some x) <> f None}).
apply finite_dec_exists.
assumption.
intro.
apply decidable_dec.
apply H0.
case H1.
intro.
pose (g := fun (x:T) => f (Some x)).
assert (Im Full_set f = Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
exists t.
constructor.
assumption.
destruct e.
exists x.
constructor.
transitivity (f None).
assumption.
symmetry; assumption.
red; intros.
destruct H2.
exists (Some x).
constructor.
assumption.
rewrite H2.
apply IHFiniteT.
intros.
pose (g := fun x:T => f (Some x)).
assert (Im Full_set f = Add (Im Full_set g) (f None)).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct x.
left.
exists t.
constructor.
assumption.
right.
auto with sets.
red; intros.
destruct H2.
destruct H2.
exists (Some x).
constructor.
assumption.
destruct H2.
exists None.
constructor.
reflexivity.
rewrite H2.
constructor.
apply IHFiniteT.
red; intro.
destruct H3.
contradiction (n x).
symmetry; assumption.
pose (g := fun (x:X) => f (f0 x)).
assert (Im Full_set f = Im Full_set g).
apply Extensionality_Ensembles.
red; split.
red; intros.
destruct H2.
destruct H1.
rewrite H3.
rewrite <- H4 with x.
exists (g0 x).
constructor.
unfold g.
reflexivity.
red; intros.
destruct H2.
exists (f0 x).
constructor.
assumption.
rewrite H2.
apply IHFiniteT.
