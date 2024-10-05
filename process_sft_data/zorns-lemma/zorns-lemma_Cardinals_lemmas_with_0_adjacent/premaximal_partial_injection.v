Require Export FunctionProperties.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import CSB.
Require Import EnsemblesSpec.
Inductive Cardinal : Type := | cardinality: Type -> Cardinal.
Fixpoint n_element_set (n:nat) : Set := match n with | O => False | S m => option (n_element_set m) end.
Definition nat_to_cardinal (n:nat) := cardinality (n_element_set n).
Definition aleph0 := cardinality nat.
Inductive eq_cardinal : Cardinal -> Cardinal -> Prop := | bij_eq_cardinal: forall {X Y:Type} (f:X->Y), bijective f -> eq_cardinal (cardinality X) (cardinality Y).
Inductive le_cardinal : Cardinal -> Cardinal -> Prop := | inj_le_cardinal: forall {X Y:Type} (f:X->Y), injective f -> le_cardinal (cardinality X) (cardinality Y).
Definition lt_cardinal (kappa lambda:Cardinal) : Prop := le_cardinal kappa lambda /\ ~ eq_cardinal kappa lambda.
Definition ge_cardinal (kappa lambda:Cardinal) : Prop := le_cardinal lambda kappa.
Definition gt_cardinal (kappa lambda:Cardinal) : Prop := lt_cardinal lambda kappa.
Require Import ClassicalChoice.
Require Import ZornsLemma.
Require Import EnsemblesImplicit.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Description.
Section le_cardinal_total.
Variable X Y:Type.
Record partial_injection : Type := { pi_dom: Ensemble X; pi_func: forall x:X, In pi_dom x -> Y; pi_inj: forall (x1 x2:X) (i1:In pi_dom x1) (i2:In pi_dom x2), pi_func x1 i1 = pi_func x2 i2 -> x1 = x2 }.
Record partial_injection_ord (pi1 pi2:partial_injection) : Prop := { pi_dom_inc: Included (pi_dom pi1) (pi_dom pi2); pi_func_ext: forall (x:X) (i1:In (pi_dom pi1) x) (i2:In (pi_dom pi2) x), pi_func pi1 x i1 = pi_func pi2 x i2 }.
End le_cardinal_total.

Lemma premaximal_partial_injection: exists x:partial_injection, premaximal partial_injection_ord x.
Proof.
apply ZornsLemmaForPreorders.
exact partial_injection_preord.
exact partial_injection_chain_ub.
