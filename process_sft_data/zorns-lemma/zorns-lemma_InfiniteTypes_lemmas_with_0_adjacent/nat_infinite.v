Require Export FiniteTypes.
Require Import EnsemblesImplicit.
Require Import ClassicalChoice.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import EnsemblesSpec.

Lemma nat_infinite: ~ FiniteT nat.
Proof.
red; intro.
assert (surjective S).
apply finite_inj_surj; trivial.
red; intros.
injection H0; trivial.
destruct (H0 0).
discriminate H1.
