Require Export FiniteTypes.
Require Import EnsemblesImplicit.
Require Import ClassicalChoice.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import EnsemblesSpec.

Lemma finite_nat_initial_segment: forall n:nat, FiniteT { m:nat | m < n }.
Proof.
intros.
apply Finite_ens_type.
rewrite <- characteristic_function_to_ensemble_is_identity.
induction n.
assert ([x:nat | S x <= 0] = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H.
contradict H.
auto with arith.
rewrite H; constructor.
assert ([x:nat | S x <= S n] = Add [x:nat | x < n] n).
apply Extensionality_Ensembles; split.
red; intros.
destruct H.
assert (x <= n); auto with arith.
apply le_lt_or_eq in H0.
case H0.
left; constructor; trivial.
right; auto with sets.
red; intros.
case H.
intros.
destruct H0; constructor.
auto with arith.
intros.
destruct H0.
constructor.
auto with arith.
rewrite H; constructor; trivial.
red; intro.
destruct H0.
contradict H0.
auto with arith.
