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

Lemma unique_FiniteT_nat_cardinal: exists! f: (forall (X:Type), FiniteT X -> nat), f False empty_finite = 0 /\ (forall (X:Type) (H:FiniteT X), f (option X) (add_finite X H) = S (f X H)) /\ (forall (X Y:Type) (H:FiniteT X) (g:X->Y) (Hinv:invertible g), f Y (bij_finite X Y g H Hinv) = f X H).
Proof.
match goal with |- @ex ?T (@unique ?T ?f) => apply -> (@unique_existence T f) end.
split.
exists FiniteT_nat_cardinal.
repeat split.
exact FiniteT_nat_cardinal_False.
exact FiniteT_nat_cardinal_option.
exact FiniteT_nat_cardinal_bijection.
red; intros f g Hf Hg.
destruct Hf as [HFalse_f [Hoption_f Hbijection_f]].
destruct Hg as [HFalse_g [Hoption_g Hbijection_g]].
extensionality X; extensionality HFinite.
generalize HFinite.
induction HFinite.
intro.
destruct (proof_irrelevance _ empty_finite HFinite).
congruence.
intro.
destruct (proof_irrelevance _ (add_finite T HFinite) HFinite0).
rewrite Hoption_f.
rewrite Hoption_g.
rewrite IHHFinite.
reflexivity.
intro.
destruct (proof_irrelevance _ (bij_finite _ _ f0 HFinite H) HFinite0).
now rewrite Hbijection_f, Hbijection_g, IHHFinite.
